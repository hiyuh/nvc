//
//  Copyright (C) 2011-2012  Nick Gasson
//
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//
//  You should have received a copy of the GNU General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.
//

#include "rt.h"
#include "util.h"
#include "lib.h"

#include <assert.h>
#include <limits.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>
#include <dlfcn.h>

#include <llvm-c/Core.h>
#include <llvm-c/BitReader.h>
#include <llvm-c/ExecutionEngine.h>

static LLVMModuleRef          module = NULL;
static LLVMExecutionEngineRef exec_engine = NULL;

static bool using_jit = true;
static void *dl_handle = NULL;

void *jit_fun_ptr(const char *name)
{
   if (using_jit) {
      LLVMValueRef fn;
      if (LLVMFindFunction(exec_engine, name, &fn))
         fatal("cannot find function %s", name);

      return LLVMGetPointerToGlobal(exec_engine, fn);
   }
   else
      return jit_var_ptr(name);
}

static char *jit_str_add(char *p, const char *s)
{
   while (*s != '\0')
      *p++ = *s++;
   return p;
}

static void jit_native_name(const char *name, char *buf, size_t len)
{
   char *p = buf;
   char ch;
   while ((ch = *(name++)) && (p < buf + len - 4)) {
      switch (ch) {
      case ':':
         p = jit_str_add(p, "_3A_");
         break;
      case '(':
         p = jit_str_add(p, "_28_");
         break;
      case ')':
         p = jit_str_add(p, "_29_");
         break;
      case '@':
         p = jit_str_add(p, "_40_");
         break;
      default:
         *p++ = ch;
      }
   }
   *p = '\0';
}

void *jit_var_ptr(const char *name)
{
   if (using_jit) {
      LLVMValueRef var = LLVMGetNamedGlobal(module, name);
      if (var == NULL)
         fatal("cannot find global %s", name);

      return LLVMGetPointerToGlobal(exec_engine, var);
   }
   else {
      dlerror();   // Clear any previous error
      char dlname[256];
      jit_native_name(name, dlname, sizeof(dlname));
      void *sym = dlsym(dl_handle, dlname);
      const char *error = dlerror();
      if (error != NULL)
         fatal("%s", error);
      return sym;
   }
}

void jit_bind_fn(const char *name, void *ptr)
{
   if (using_jit) {
      LLVMValueRef fn;
      if (LLVMFindFunction(exec_engine, name, &fn))
         return;

      LLVMAddGlobalMapping(exec_engine, fn, ptr);
   }
}

static void jit_init_llvm(const char *path)
{
   char *error;
   LLVMMemoryBufferRef buf;
   if (LLVMCreateMemoryBufferWithContentsOfFile(path, &buf, &error))
      fatal("error reading bitcode from %s: %s", path, error);

   if (LLVMParseBitcode(buf, &module, &error))
      fatal("error parsing bitcode: %s", error);

   LLVMDisposeMemoryBuffer(buf);

   LLVMInitializeNativeTarget();
   LLVMLinkInJIT();

   if (LLVMCreateExecutionEngineForModule(&exec_engine, module, &error))
      fatal("error creating execution engine: %s", error);
}

static void jit_init_native(const char *path)
{
   if ((dl_handle = dlopen(path, RTLD_LAZY)) == NULL)
      fatal("%s: %s", path, dlerror());
}

static time_t jit_mod_time(const char *path)
{
   struct stat st;
   if (stat(path, &st) == -1) {
      if (errno == ENOENT)
         return 0;
      else
         fatal_errno("%s", path);
   }
   return st.st_mtime;
}

void jit_init(ident_t top)
{
   ident_t orig = ident_strip(top, ident_new(".elab"));
   ident_t final = ident_prefix(orig, ident_new("final"), '.');

   char bc_fname[64], so_fname[64];;
   snprintf(bc_fname, sizeof(bc_fname), "_%s.bc", istr(final));
   // TODO: different on OS X, etc.
#if defined __CYGWIN__
   snprintf(so_fname, sizeof(so_fname), "_%s.dll", istr(final));
#else
   snprintf(so_fname, sizeof(so_fname), "_%s.so", istr(final));
#endif

   char bc_path[PATH_MAX], so_path[PATH_MAX];
   lib_realpath(lib_work(), bc_fname, bc_path, sizeof(bc_path));
   lib_realpath(lib_work(), so_fname, so_path, sizeof(so_path));

   using_jit = (jit_mod_time(bc_path) > jit_mod_time(so_path));

   if (using_jit)
      jit_init_llvm(bc_path);
   else
      jit_init_native(so_path);
}

void jit_shutdown(void)
{
   if (using_jit)
      LLVMDisposeExecutionEngine(exec_engine);
   else
      dlclose(dl_handle);
}
