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

#include "util.h"
#include "phase.h"
#include "lib.h"
#include "rt/signal.h"

#include <stdlib.h>
#include <string.h>

#include <llvm-c/Core.h>
#include <llvm-c/BitWriter.h>
#include <llvm-c/ExecutionEngine.h>
#include <llvm-c/Analysis.h>
#include <llvm-c/Transforms/Scalar.h>
#include <llvm-c/Transforms/IPO.h>

#undef NDEBUG
#include <assert.h>

static LLVMModuleRef  module = NULL;
static LLVMBuilderRef builder = NULL;
static LLVMValueRef   mod_name = NULL;

static ident_t var_offset_i = NULL;
static ident_t local_var_i = NULL;
static ident_t sig_struct_i = NULL;
static ident_t foreign_i = NULL;

// Linked list of entry points to a process
// These correspond to wait statements
struct proc_entry {
   int               state_num;
   tree_t            wait;
   LLVMBasicBlockRef bb;
   struct proc_entry *next;
};

// Linked list of named blocks such as loops
struct block_list {
   ident_t           name;
   LLVMBasicBlockRef exit_bb;
   struct block_list *next;
};

// Code generation context for a process or function
struct cgen_ctx {
   struct proc_entry *entry_list;
   struct block_list *blocks;
   LLVMValueRef      state;
   LLVMValueRef      fn;
   tree_t            proc;
   tree_t            fdecl;
};

static LLVMValueRef cgen_expr(tree_t t, struct cgen_ctx *ctx);
static void cgen_stmt(tree_t t, struct cgen_ctx *ctx);
static LLVMValueRef cgen_get_var(tree_t decl, struct cgen_ctx *ctx);
static bool cgen_const_bounds(type_t type);
static LLVMValueRef cgen_array_data_ptr(type_t type, LLVMValueRef var);
static LLVMTypeRef cgen_signal_type(void);

static LLVMValueRef llvm_int1(bool b)
{
   return LLVMConstInt(LLVMInt1Type(), b, false);
}

static LLVMValueRef llvm_int8(int32_t i)
{
   return LLVMConstInt(LLVMInt8Type(), i, false);
}

static LLVMValueRef llvm_int32(int32_t i)
{
   return LLVMConstInt(LLVMInt32Type(), i, false);
}

static LLVMValueRef llvm_int64(int64_t i)
{
   return LLVMConstInt(LLVMInt64Type(), i, false);
}

static LLVMTypeRef llvm_void_ptr(void)
{
   return LLVMPointerType(LLVMInt8Type(), 0);
}

static LLVMValueRef llvm_void_cast(LLVMValueRef ptr)
{
   return LLVMBuildPointerCast(builder, ptr, llvm_void_ptr(), "");
}

static LLVMValueRef llvm_sizeof(LLVMTypeRef type)
{
   return LLVMBuildIntCast(builder, LLVMSizeOf(type),
                           LLVMInt32Type(), "");
}

static LLVMValueRef llvm_fn(const char *name)
{
   LLVMValueRef fn = LLVMGetNamedFunction(module, name);
   assert(fn != NULL);
   return fn;
}

static void llvm_str(LLVMValueRef *chars, size_t n, const char *str)
{
   size_t i;
   for (i = 0; i < n; i++)
      chars[i] = llvm_int8(*str ? *(str++) : '\0');
}

#if 0
static void debug_out(LLVMValueRef val)
{
   LLVMValueRef args[] = { val };
   LLVMBuildCall(builder, llvm_fn("_debug_out"),
                 args, ARRAY_LEN(args), "");
}
#endif

static int bit_width(type_t t)
{
   switch (type_kind(t)) {
   case T_INTEGER:
   case T_PHYSICAL:
      {
         range_t r = type_dim(t, 0);
         uint64_t elements = assume_int(r.right) - assume_int(r.left);

         if (elements <= 2)
            return 1;
         if (elements <= 0xffull)
            return 8;
         else if (elements <= 0xffffull)
            return 16;
         else if (elements <= 0xffffffffull)
            return 32;
         else
            return 64;
      }

   case T_SUBTYPE:
      return bit_width(type_base(t));

   case T_ENUM:
      {
         unsigned lits = type_enum_literals(t);

         if (lits <= 2)
            return 1;
         if (lits <= 256)
            return 8;
         else if (lits <= 65356)
            return 16;
         else
            return 32;
      }

   default:
      assert(false);
   }
}

static LLVMTypeRef llvm_uarray_type(LLVMTypeRef base)
{
   // Unconstrained arrays are represented by a structure
   // containing the left and right indices, a flag indicating
   // direction, and a pointer to the array data

   LLVMTypeRef fields[] = {
      LLVMPointerType(base, 0),
      LLVMInt32Type(),      // Left
      LLVMInt32Type(),      // Right
      LLVMInt8Type()        // Direction
   };

   return LLVMStructType(fields, ARRAY_LEN(fields), false);
}

static LLVMTypeRef llvm_type(type_t t)
{
   switch (type_kind(t)) {
   case T_INTEGER:
   case T_PHYSICAL:
   case T_ENUM:
      return LLVMIntType(bit_width(t));

   case T_SUBTYPE:
      if (!type_is_array(t))
         return llvm_type(type_base(t));

      // Fall-through
   case T_CARRAY:
   case T_UARRAY:
      {
         if (cgen_const_bounds(t)) {
            int nelems = 1;
            unsigned i;
            for (i = 0; i < type_dims(t); i++) {
               int64_t low, high;
               range_bounds(type_dim(t, i), &low, &high);
               if (high < low)
                  nelems = 0;
               else
                  nelems *= (high - low + 1);
            }
            return LLVMArrayType(llvm_type(type_elem(t)), nelems);
         }
         else {
            return llvm_uarray_type(llvm_type(type_elem(t)));
         }
      }

   default:
      assert(false);
   }
}

static const char *cgen_mangle_func_name(tree_t decl)
{
   tree_t foreign;
   static char buf[512];
   const char *end = buf + sizeof(buf);
   char *p = buf;
   type_t type = tree_type(decl);
   unsigned i;

   foreign = tree_attr_tree(decl, foreign_i);
   if (foreign != NULL) {
      assert(tree_kind(foreign) == T_AGGREGATE);

      for (i = 0; i < tree_assocs(foreign); i++) {
         assoc_t a;
         tree_t ch;

         a = tree_assoc(foreign, i);
         assert(a.kind == A_POS);
         assert(tree_kind(a.value) == T_REF);

         ch = tree_ref(a.value);
         assert(tree_kind(ch) == T_ENUM_LIT);

         *p++ = tree_pos(ch);
      }

      *p = '\0';
   }
   else {
      p += snprintf(p, end - p, "%s", istr(tree_ident(decl)));
      for (i = 0; i < type_params(type); i++) {
         type_t param = type_param(type, i);
         p += snprintf(p, end - p, "$%s", istr(type_ident(param)));
      }
   }

   return buf;
}

static bool cgen_is_const(tree_t t)
{
   if (tree_kind(t) == T_AGGREGATE) {
      bool is_const = true;
      unsigned i;
      for (i = 0; i < tree_assocs(t); i++) {
         assoc_t a = tree_assoc(t, i);
         is_const = is_const && cgen_is_const(a.value);
      }
      return is_const;
   }
   else
      return (tree_kind(t) == T_LITERAL
              || (tree_kind(t) == T_REF
                  && tree_kind(tree_ref(t)) == T_ENUM_LIT));
}

static bool cgen_const_bounds(type_t type)
{
   if (type_kind(type) == T_UARRAY)
      return false;
   else {
      range_t r = type_dim(type, 0);
      return cgen_is_const(r.left) && cgen_is_const(r.right);
   }
}

static class_t cgen_get_class(tree_t decl)
{
   switch (tree_kind(decl)) {
   case T_VAR_DECL:
      return C_VARIABLE;
   case T_SIGNAL_DECL:
      return C_SIGNAL;
   case T_CONST_DECL:
      return C_CONSTANT;
   default:
      return tree_class(decl);
   }
}

static LLVMValueRef cgen_array_meta(type_t type,
                                    LLVMValueRef left, LLVMValueRef right,
                                    LLVMValueRef kind, LLVMValueRef ptr)
{
   LLVMTypeRef base = llvm_type(type_elem(type));
   LLVMValueRef var = LLVMGetUndef(llvm_uarray_type(base));
   var = LLVMBuildInsertValue(builder, var, ptr, 0, "");
   var = LLVMBuildInsertValue(builder, var, left, 1, "");
   var = LLVMBuildInsertValue(builder, var, right, 2, "");
   var = LLVMBuildInsertValue(builder, var, kind, 3, "");
   return var;
}

static LLVMValueRef cgen_range_low(range_t r, struct cgen_ctx *ctx)
{
   return cgen_expr(r.kind == RANGE_TO ? r.left : r.right, ctx);
}

static LLVMValueRef cgen_uarray_low(LLVMValueRef array)
{
   LLVMValueRef dir =
      LLVMBuildExtractValue(builder, array, 3, "dir");
   LLVMValueRef is_downto =
      LLVMBuildICmp(builder, LLVMIntEQ, dir,
                    llvm_int8(RANGE_DOWNTO), "is_downto");
   LLVMValueRef left =
      LLVMBuildExtractValue(builder, array, 1, "left");
   LLVMValueRef right =
      LLVMBuildExtractValue(builder, array, 2, "right");
   return LLVMBuildSelect(builder, is_downto, right, left, "low");
}

static LLVMValueRef cgen_array_dir(type_t type, LLVMValueRef var)
{
   if (!cgen_const_bounds(type))
      return LLVMBuildExtractValue(builder, var, 3, "dir");
   else
      return llvm_int8(type_dim(type, 0).kind);
}

static LLVMValueRef cgen_array_left(type_t type, LLVMValueRef var)
{
   if (!cgen_const_bounds(type))
      return LLVMBuildExtractValue(builder, var, 1, "left");
   else
      return llvm_int32(assume_int(type_dim(type, 0).left));
}

static LLVMValueRef cgen_array_right(type_t type, LLVMValueRef var)
{
   if (!cgen_const_bounds(type))
      return LLVMBuildExtractValue(builder, var, 2, "right");
   else
      return llvm_int32(assume_int(type_dim(type, 0).right));
}

static LLVMValueRef cgen_array_len(type_t type, LLVMValueRef data)
{
   if (cgen_const_bounds(type)) {
      int n_elems = 1;
      unsigned i;
      for (i = 0; i < type_dims(type); i++) {
         int64_t low, high;
         range_bounds(type_dim(type, i), &low, &high);

         if (high < low)
            n_elems = 0;
         else
            n_elems *= (high - low + 1);
      }
      return llvm_int32(n_elems);
   }
   else {
      // Argument must be a structure where the first two fields are the
      // left and right indices
      LLVMValueRef downto = LLVMBuildICmp(
         builder, LLVMIntEQ,
         LLVMBuildExtractValue(builder, data, 3, "dir"),
         llvm_int8(RANGE_DOWNTO),
         "downto");
      LLVMValueRef left  = LLVMBuildExtractValue(builder, data, 1, "left");
      LLVMValueRef right = LLVMBuildExtractValue(builder, data, 2, "right");
      LLVMValueRef diff  =
         LLVMBuildSelect(builder, downto,
                         LLVMBuildSub(builder, left, right, ""),
                         LLVMBuildSub(builder, right, left, ""),
                         "diff");
      LLVMValueRef len = LLVMBuildAdd(builder, diff, llvm_int32(1), "len");
      LLVMValueRef neg = LLVMBuildICmp(builder, LLVMIntSLT, len,
                                       llvm_int32(0), "negative");
      return LLVMBuildSelect(builder, neg, llvm_int32(0), len, "len_clamp");
   }
}

static LLVMValueRef cgen_tmp_var(tree_t d, struct cgen_ctx *ctx)
{
   type_t type;
   range_t r;
   LLVMValueRef kind_ll;
   param_t p;
   LLVMValueRef uarray;
   LLVMValueRef downto, left, right, diff, length, buf, ptr;
   LLVMTypeRef base_type, ptr_type;

   type = tree_type(d);

   // Handle case where array size is not known until run time
   if (type_is_array(type) && !cgen_const_bounds(type)) {
      // Allocate the array for the process temporary heap and
      // wrap in a metadata struct

      r = type_dim(type, 0);
      if (r.kind == RANGE_DYN) {
         // This can only appear when using 'RANGE
         assert(tree_kind(r.left) == T_FCALL);
         p = tree_param(r.left, 0);
         assert(tree_kind(p.value) == T_REF);

         uarray = cgen_get_var(tree_ref(p.value), ctx);

         kind_ll = LLVMBuildExtractValue(builder, uarray, 3, "dir");
      }
      else
         kind_ll = llvm_int8(r.kind);

      downto =
         LLVMBuildICmp(builder, LLVMIntEQ,
                       kind_ll, llvm_int8(RANGE_DOWNTO), "downto");

      left   = cgen_expr(r.left, ctx);
      right  = cgen_expr(r.right, ctx);

      diff =
         LLVMBuildSelect(builder, downto,
                         LLVMBuildSub(builder, left, right, ""),
                         LLVMBuildSub(builder, right, left, ""), "");

      length =
         LLVMBuildAdd(builder, diff, llvm_int32(1), "length");

      base_type = llvm_type(type_elem(type));
      ptr_type  = LLVMPointerType(base_type, 0);

      buf =
         LLVMBuildArrayAlloca(builder, base_type, length, "buf");

      ptr = LLVMBuildPointerCast(builder, buf, ptr_type, "");

      return cgen_array_meta(type, left, right, kind_ll, ptr);
   }
   else {
      const char *name =
         (tree_kind(d) == T_VAR_DECL ? istr(tree_ident(d)) : "");
      return LLVMBuildAlloca(builder, llvm_type(tree_type(d)), name);
   }
}

static LLVMValueRef cgen_local_var(tree_t d, struct cgen_ctx *ctx)
{
   if (tree_has_value(d) && type_is_array(tree_type(d))) {
      // Generating the initial value will also allocate storage
      return cgen_expr(tree_value(d), ctx);
   }
   else {
      LLVMValueRef var = cgen_tmp_var(d, ctx);

      if (tree_has_value(d))
         LLVMBuildStore(builder, cgen_expr(tree_value(d), ctx), var);

      return var;
   }
}

static LLVMValueRef cgen_array_off(LLVMValueRef off, LLVMValueRef array,
                                   type_t type, struct cgen_ctx *ctx,
                                   unsigned dim)
{
   // Convert VHDL offset 'off' to a zero-based LLVM array offset

   LLVMValueRef low;
   range_t r;
   LLVMValueRef zero_based;

   if (!cgen_const_bounds(type)) {
      assert(array != NULL);
      low = cgen_uarray_low(array);
   }
   else {
      r = type_dim(type, dim);
      low = cgen_range_low(r, ctx);
   }

   zero_based = LLVMBuildSub(builder, off, low, "");

   // Array offsets are always 32-bit
   return LLVMBuildIntCast(builder, zero_based, LLVMInt32Type(), "");
}

static LLVMValueRef cgen_get_slice(LLVMValueRef array, type_t type,
                                   range_t r, struct cgen_ctx *ctx)
{
   LLVMValueRef low, off, data, ptr;

   // Construct a new array sharing the same memory as `array' but offset
   // by `range'

   assert(type_is_array(type));

   low = cgen_range_low(r, ctx);
   off = cgen_array_off(low, array, type, ctx, 0);
   data = cgen_array_data_ptr(type, array);

   ptr = LLVMBuildGEP(builder, data, &off, 1, "");

   bool unwrap = cgen_is_const(r.left) && cgen_is_const(r.right);

   if (unwrap)
      return ptr;
   else
      return cgen_array_meta(type,
                             cgen_expr(r.left, ctx),
                             cgen_expr(r.right, ctx),
                             llvm_int8(r.kind),
                             ptr);
}

static LLVMValueRef cgen_array_signal_ptr(tree_t decl, LLVMValueRef elem)
{
   LLVMValueRef indexes[] = { llvm_int32(0), elem };

   assert(tree_kind(decl) == T_SIGNAL_DECL);

   return LLVMBuildGEP(builder, tree_attr_ptr(decl, sig_struct_i),
                       indexes, ARRAY_LEN(indexes), "");
}

static LLVMValueRef cgen_get_var(tree_t decl, struct cgen_ctx *ctx)
{
   void *local;
   int offset;

   local = tree_attr_ptr(decl, local_var_i);
   if (local != NULL)
      return (LLVMValueRef)local;

   assert(tree_kind(decl) == T_VAR_DECL);

   offset = tree_attr_int(decl, var_offset_i, -1);
   assert(offset != -1);

   return LLVMBuildStructGEP(builder, ctx->state, offset, "");
}

static void cgen_array_copy(type_t src_type, type_t dest_type,
                            LLVMValueRef src, LLVMValueRef dst,
                            LLVMValueRef offset)
{
   LLVMValueRef src_dir, dst_dir, opposite_dir, ll_n_elems, src_ptr;
   LLVMValueRef args[6];

   src_dir = cgen_array_dir(src_type, src);
   dst_dir = cgen_array_dir(dest_type, dst);

   opposite_dir =
      LLVMBuildICmp(builder, LLVMIntNE, src_dir, dst_dir, "opp_dir");

   ll_n_elems = cgen_array_len(src_type, src);

   if (!cgen_const_bounds(dest_type))
      dst = cgen_array_data_ptr(dest_type, dst);

   src_ptr = cgen_array_data_ptr(src_type, src);

   if (offset == NULL)
      offset = llvm_int32(0);

   args[0] = llvm_void_cast(dst);
   args[1] = llvm_void_cast(src_ptr);
   args[2] = offset;
   args[3] = ll_n_elems;
   args[4] = llvm_sizeof(llvm_type(type_elem(dest_type)));
   args[5] = opposite_dir;
   LLVMBuildCall(builder, llvm_fn("_array_copy"),
                 args, ARRAY_LEN(args), "");
}

static void cgen_prototype(tree_t t, LLVMTypeRef *args, bool procedure)
{
   unsigned i;
   for (i = 0; i < tree_ports(t); i++) {
      tree_t p = tree_port(t, i);
      switch (tree_class(p)) {
      case C_SIGNAL:
         args[i] = LLVMPointerType(cgen_signal_type(), 0);
         break;

      case C_VARIABLE:
      case C_DEFAULT:
      case C_CONSTANT:
         {
            type_t type = tree_type(p);
            port_mode_t mode = tree_port_mode(p);
            bool array = type_is_array(type);
            bool need_ptr = ((mode == PORT_OUT || mode == PORT_INOUT)
                             && !array);
            if (need_ptr)
               args[i] = LLVMPointerType(llvm_type(type), 0);
            else if (array && (type_kind(type) != T_UARRAY))
               args[i] = LLVMPointerType(llvm_type(type), 0);
            else
               args[i] = llvm_type(type);
         }
         break;

      case C_FILE:
         assert(false);
      }
   }
}

static LLVMValueRef cgen_fdecl(tree_t t)
{
   const char *mangled = cgen_mangle_func_name(t);
   LLVMValueRef fn = LLVMGetNamedFunction(module, mangled);
   if (fn != NULL)
      return fn;
   else {
      type_t ftype = tree_type(t);

      LLVMTypeRef atypes[tree_ports(t)];
      cgen_prototype(t, atypes, false);

      return LLVMAddFunction(
         module,
         cgen_mangle_func_name(t),
         LLVMFunctionType(llvm_type(type_result(ftype)),
                          atypes,
                          type_params(ftype),
                          false));
   }
}

static LLVMValueRef cgen_pdecl(tree_t t)
{
   const char *mangled = cgen_mangle_func_name(t);
   LLVMValueRef fn = LLVMGetNamedFunction(module, mangled);
   if (fn != NULL)
      return fn;
   else {
      type_t ptype = tree_type(t);

      LLVMTypeRef atypes[tree_ports(t)];
      cgen_prototype(t, atypes, true);

      return LLVMAddFunction(
         module,
         cgen_mangle_func_name(t),
         LLVMFunctionType(llvm_void_ptr(),
                          atypes,
                          type_params(ptype),
                          false));
   }
}

static LLVMValueRef cgen_literal(tree_t t)
{
   literal_t l = tree_literal(t);
   switch (l.kind) {
   case L_INT:
      return LLVMConstInt(llvm_type(tree_type(t)), l.i, false);
   default:
      abort();
   }
}

static LLVMValueRef cgen_array_signal_ref(tree_t decl, type_t slice_type,
                                          struct cgen_ctx *ctx, bool last_value)
{
   type_t type;
   LLVMValueRef tmp;
   char name[256];
   range_t r;
   LLVMValueRef left_off, right_off;
   LLVMValueRef left_abs, right_abs;
   LLVMValueRef s_signal;
   LLVMValueRef indexes[2];
   LLVMValueRef p_signal;
   LLVMValueRef p_tmp;
   LLVMValueRef args[5];

   type = tree_type(decl);
   assert(type_kind(type) == T_CARRAY);

   // Copy the resolved signal into a temporary array
   tmp = LLVMBuildAlloca(builder, llvm_type(slice_type),
                         istr(tree_ident(decl)));

   snprintf(name, sizeof(name), "%s_vec_load",
            istr(type_ident(type_elem(tree_type(decl)))));

   r = type_dim(slice_type, 0);
   left_off =
      cgen_expr(r.kind == RANGE_TO ? r.left : r.right, ctx);
   right_off =
      cgen_expr(r.kind == RANGE_TO ? r.right : r.left, ctx);

   left_abs = cgen_array_off(left_off, NULL, type, ctx, 0);
   right_abs = cgen_array_off(right_off, NULL, type, ctx, 0);

   s_signal = tree_attr_ptr(decl, sig_struct_i);
   indexes[0] = llvm_int32(0);
   indexes[1] = llvm_int32(0);
   p_signal = LLVMBuildGEP(builder, s_signal,
                           indexes, ARRAY_LEN(indexes), "");
   p_tmp = LLVMBuildGEP(builder, tmp,
                        indexes, ARRAY_LEN(indexes), "");

   args[0] = p_signal;
   args[1] = p_tmp;
   args[2] = left_abs;
   args[3] = right_abs;
   args[4] = llvm_int1(last_value);
   LLVMBuildCall(builder, llvm_fn(name), args, ARRAY_LEN(args), "");
   return tmp;
}

static LLVMValueRef cgen_scalar_signal_flag(tree_t signal, int flag)
{
   LLVMValueRef signal_struct = tree_attr_ptr(signal, sig_struct_i);
   LLVMValueRef bit = llvm_int8(flag);
   LLVMValueRef ptr =
      LLVMBuildStructGEP(builder, signal_struct, SIGNAL_FLAGS, "");
   LLVMValueRef deref = LLVMBuildLoad(builder, ptr, "");
   LLVMValueRef masked = LLVMBuildAnd(builder, deref, bit, "");
   return LLVMBuildICmp(builder, LLVMIntEQ, masked, bit, "");
}

static LLVMValueRef cgen_array_signal_flag(tree_t signal, int flag)
{
   LLVMValueRef bit;
   int64_t low, high;
   LLVMValueRef result;
   int i;
   LLVMValueRef struct_ptr, flags_ptr, deref, masked;

   // Need to OR the flag for each sub-element

   bit = llvm_int8(flag);

   range_bounds(type_dim(tree_type(signal), 0), &low, &high);

   result = llvm_int8(0);
   for (i = 0; i < high - low + 1; i++) {
      struct_ptr =
         cgen_array_signal_ptr(signal, llvm_int32(i));
      flags_ptr =
         LLVMBuildStructGEP(builder, struct_ptr, SIGNAL_FLAGS, "");
      deref = LLVMBuildLoad(builder, flags_ptr, "");
      masked = LLVMBuildAnd(builder, deref, bit, "");
      result = LLVMBuildOr(builder, result, masked, "");
   }

   return LLVMBuildICmp(builder, LLVMIntEQ, result, bit, "");
}

static LLVMValueRef cgen_signal_flag(tree_t ref, int flag)
{
   tree_t sig_decl = tree_ref(ref);
   if (type_kind(tree_type(sig_decl)) == T_CARRAY)
      return cgen_array_signal_flag(sig_decl, flag);
   else
      return cgen_scalar_signal_flag(sig_decl, flag);
}

static LLVMValueRef cgen_last_value(tree_t signal, struct cgen_ctx *ctx)
{
   tree_t sig_decl = tree_ref(signal);

   if (type_kind(tree_type(sig_decl)) == T_CARRAY) {
      type_t type = tree_type(sig_decl);
      return cgen_array_signal_ref(sig_decl, type, ctx, true);
   }
   else {
      LLVMValueRef signal = tree_attr_ptr(sig_decl, sig_struct_i);
      LLVMValueRef ptr =
         LLVMBuildStructGEP(builder, signal, SIGNAL_LAST_VALUE, "");
      LLVMValueRef deref = LLVMBuildLoad(builder, ptr, "");
      return LLVMBuildIntCast(builder, deref,
                              llvm_type(tree_type(sig_decl)), "");
   }
}

static LLVMValueRef cgen_uarray_asc(LLVMValueRef uarray)
{
   return LLVMBuildICmp(
      builder, LLVMIntEQ,
      LLVMBuildExtractValue(builder, uarray, 3, "dir"),
      llvm_int8(RANGE_TO),
      "ascending");
}

static void cgen_call_args(tree_t t, LLVMValueRef *args, struct cgen_ctx *ctx)
{
   tree_t decl = tree_ref(t);
   ident_t builtin = tree_attr_str(decl, ident_new("builtin"));

   unsigned i;
   for (i = 0; i < tree_params(t); i++) {
      param_t p = tree_param(t, i);
      if (builtin == NULL && tree_class(tree_port(decl, i)) == C_SIGNAL) {
         tree_t decl_g;
         // Pass a pointer to the global signal structure
         assert(tree_kind(p.value) == T_REF);
         decl_g = tree_ref(p.value);
         args[i] = tree_attr_ptr(decl_g, sig_struct_i);
         assert(args[i] != NULL);
      }
      else {
         type_t type, formal_type;
         bool need_wrap;

         args[i] = NULL;

         type = tree_type(p.value);

         // If this is a scalar out or inout parameter then we need
         // to pass a pointer rather than the value
         if (builtin == NULL) {
            tree_t port = tree_port(decl, i);
            port_mode_t mode = tree_port_mode(port);
            bool need_ptr = ((mode == PORT_OUT || mode == PORT_INOUT)
                             && !type_is_array(type));
            if (need_ptr)
               args[i] = cgen_get_var(tree_ref(p.value), ctx);

            formal_type = tree_type(port);
         }
         else
            formal_type = type;

         if (args[i] == NULL)
            args[i] = cgen_expr(p.value, ctx);

         // If we are passing a constrained array argument wrap it in
         // a structure with its metadata. Note we don't need to do
         // this for unconstrained arrays as they are already wrapped.
         need_wrap =
            (type_kind(formal_type) == T_UARRAY)
            && cgen_const_bounds(type)
            && (builtin == NULL);

         if (need_wrap) {
            range_t r = type_dim(type, 0);

            LLVMTypeRef ptr_type =
               LLVMPointerType(llvm_type(type_elem(type)), 0);

            args[i] = cgen_array_meta(
               type,
               llvm_int32(assume_int(r.left)),
               llvm_int32(assume_int(r.right)),
               llvm_int8(r.kind),
               LLVMBuildPointerCast(builder, args[i], ptr_type, ""));
         }

         // If we are passing an unconstrained array actual to a
         // constrained formal then we need to unwrap the array
         if ((type_kind(formal_type) == T_CARRAY) && (builtin == NULL)) {
            LLVMValueRef ptr = args[i];
            if (!cgen_const_bounds(type)) {
               // XXX: insert bounds checking here
               ptr = LLVMBuildExtractValue(builder, args[i], 0, "aptr");
            }

            LLVMTypeRef lt = LLVMPointerType(llvm_type(formal_type), 0);
            args[i] = LLVMBuildPointerCast(builder, ptr, lt, "");
         }
      }
   }
}

static LLVMValueRef cgen_array_rel(LLVMValueRef lhs, LLVMValueRef rhs,
                                   type_t left_type, type_t right_type,
                                   LLVMIntPredicate pred, struct cgen_ctx *ctx)
{
   LLVMValueRef left_len, right_len;
   LLVMValueRef left_base, right_base;
   LLVMValueRef ldir, rdir;
   LLVMValueRef l_downto, r_downto;
   LLVMValueRef i;
   LLVMBasicBlockRef test_bb, body_bb, exit_bb;
   LLVMValueRef i_loaded;
   LLVMValueRef len_ge_l, len_ge_r;
   LLVMValueRef i_plus_1;
   LLVMValueRef l_off_down, r_off_down;
   LLVMValueRef l_off, r_off;
   LLVMValueRef l_ptr, r_ptr;
   LLVMValueRef l_val, r_val;
   LLVMValueRef cmp, eq, inc;
   LLVMValueRef phi;
   LLVMValueRef values[2];
   LLVMBasicBlockRef bbs[2];

   // Behaviour of relational operators on arrays is described in
   // LRM 93 section 7.2.2

   left_len  = cgen_array_len(left_type, lhs);
   right_len = cgen_array_len(right_type, rhs);

   left_base  = cgen_array_data_ptr(left_type, lhs);
   right_base = cgen_array_data_ptr(right_type, rhs);

   ldir = cgen_array_dir(left_type, lhs);
   rdir = cgen_array_dir(right_type, rhs);

   l_downto = LLVMBuildICmp(builder, LLVMIntEQ, ldir,
                            llvm_int8(RANGE_DOWNTO), "l_downto");
   r_downto = LLVMBuildICmp(builder, LLVMIntEQ, rdir,
                                         llvm_int8(RANGE_DOWNTO), "r_downto");

   i = LLVMBuildAlloca(builder, LLVMInt32Type(), "i");
   LLVMBuildStore(builder, llvm_int32(0), i);

   test_bb = LLVMAppendBasicBlock(ctx->fn, "rel_test");
   body_bb = LLVMAppendBasicBlock(ctx->fn, "rel_body");
   exit_bb = LLVMAppendBasicBlock(ctx->fn, "rel_exit");

   LLVMBuildBr(builder, test_bb);

   // Loop test

   LLVMPositionBuilderAtEnd(builder, test_bb);

   i_loaded = LLVMBuildLoad(builder, i, "i");
   len_ge_l = LLVMBuildICmp(builder, LLVMIntUGE, i_loaded,
                            left_len, "len_ge_l");
   len_ge_r = LLVMBuildICmp(builder, LLVMIntUGE, i_loaded,
                                         right_len, "len_ge_r");
   LLVMBuildCondBr(builder, LLVMBuildOr(builder, len_ge_l, len_ge_r, ""),
                   exit_bb, body_bb);

   // Loop body

   LLVMPositionBuilderAtEnd(builder, body_bb);

   i_plus_1   = LLVMBuildAdd(builder, i_loaded, llvm_int32(1), "");
   l_off_down = LLVMBuildSub(builder, left_len, i_plus_1, "");
   r_off_down = LLVMBuildSub(builder, right_len, i_plus_1, "");

   l_off = LLVMBuildSelect(builder, l_downto,
                           l_off_down, i_loaded, "l_off");
   r_off = LLVMBuildSelect(builder, r_downto,
                           r_off_down, i_loaded, "r_off");

   l_ptr = LLVMBuildGEP(builder, left_base,
                        &l_off, 1, "l_ptr");
   r_ptr = LLVMBuildGEP(builder, right_base,
                        &r_off, 1, "r_ptr");

   l_val = LLVMBuildLoad(builder, l_ptr, "l_val");
   r_val = LLVMBuildLoad(builder, r_ptr, "r_val");

   cmp = LLVMBuildICmp(builder, pred, l_val, r_val, "cmp");
   eq  = LLVMBuildICmp(builder, LLVMIntEQ, l_val, r_val, "eq");

   inc = LLVMBuildAdd(builder, i_loaded, llvm_int32(1), "inc");
   LLVMBuildStore(builder, inc, i);

   LLVMBuildCondBr(builder, eq, test_bb, exit_bb);

   // Epilogue

   LLVMPositionBuilderAtEnd(builder, exit_bb);

   phi = LLVMBuildPhi(builder, LLVMInt1Type(), "arel");

   values[0] = cmp;
   values[1] = len_ge_l;
   bbs[0] = body_bb;
   bbs[1] = test_bb;
   LLVMAddIncoming(phi, values, bbs, 2);

   return phi;
}

static LLVMValueRef cgen_agg_bound(tree_t t, bool low, int32_t def,
                                   struct cgen_ctx *ctx)
{
   LLVMValueRef result;
   unsigned i;
   assoc_t a;
   LLVMValueRef this;
   LLVMIntPredicate pred;
   LLVMValueRef cmp;

   assert(tree_kind(t) == T_AGGREGATE);

   result = llvm_int32(def);

   for (i = 0; i < tree_assocs(t); i++) {
      a = tree_assoc(t, i);
      this = NULL;
      switch (a.kind) {
         case A_NAMED:
            this = cgen_expr(a.name, ctx);
            break;

         case A_RANGE:
            if ((low && a.range.kind == RANGE_TO)
                || (!low && a.range.kind == RANGE_DOWNTO))
               this = cgen_expr(a.range.left, ctx);
            else
               this = cgen_expr(a.range.right, ctx);
            break;

         default:
            assert(false);
      }

      pred = (low ? LLVMIntSLT : LLVMIntSGT);
      cmp = LLVMBuildICmp(builder, pred, this, result, "");
      result = LLVMBuildSelect(builder, cmp, this, result, "");
   }

   return result;
}

static LLVMValueRef cgen_instance_name(tree_t ref)
{
   tree_t decl = tree_ref(ref);

   LLVMValueRef signal = tree_attr_ptr(decl, sig_struct_i);
   LLVMValueRef res = LLVMBuildAlloca(builder,
                                      llvm_uarray_type(LLVMInt8Type()),
                                      "inst_name");
   LLVMValueRef args[] = {
      llvm_void_cast(signal),
      res
   };
   LLVMBuildCall(builder, llvm_fn("_inst_name"), args, ARRAY_LEN(args), "");
   return LLVMBuildLoad(builder, res, "");
}

static LLVMValueRef cgen_fcall(tree_t t, struct cgen_ctx *ctx)
{
   tree_t decl;
   ident_t builtin;
   LLVMValueRef args[tree_params(t)];

   decl = tree_ref(t);
   assert(tree_kind(decl) == T_FUNC_DECL
          || tree_kind(decl) == T_FUNC_BODY);

   builtin = tree_attr_str(decl, ident_new("builtin"));

   // Special attributes
   if (builtin) {
      if (icmp(builtin, "event"))
         return cgen_signal_flag(tree_param(t, 0).value, SIGNAL_F_EVENT);
      else if (icmp(builtin, "active"))
         return cgen_signal_flag(tree_param(t, 0).value, SIGNAL_F_ACTIVE);
      else if (icmp(builtin, "last_value"))
         return cgen_last_value(tree_param(t, 0).value, ctx);
      else if (icmp(builtin, "agg_low"))
         return cgen_agg_bound(tree_param(t, 0).value, true, INT32_MAX, ctx);
      else if (icmp(builtin, "agg_high"))
         return cgen_agg_bound(tree_param(t, 0).value, false, INT32_MIN, ctx);
      else if (icmp(builtin, "instance_name"))
         return cgen_instance_name(tree_param(t, 0).value);
   }

   cgen_call_args(t, args, ctx);

   // Regular builtin functions
   if (builtin) {
      type_t arg_type = tree_type(tree_param(t, 0).value);

      if (icmp(builtin, "mul"))
         return LLVMBuildMul(builder, args[0], args[1], "");
      else if (icmp(builtin, "add"))
         return LLVMBuildAdd(builder, args[0], args[1], "");
      else if (icmp(builtin, "sub"))
         return LLVMBuildSub(builder, args[0], args[1], "");
      else if (icmp(builtin, "div"))
         return LLVMBuildSDiv(builder, args[0], args[1], "");
      else if (icmp(builtin, "eq"))
         return LLVMBuildICmp(builder, LLVMIntEQ, args[0], args[1], "");
      else if (icmp(builtin, "neq"))
         return LLVMBuildICmp(builder, LLVMIntNE, args[0], args[1], "");
      else if (icmp(builtin, "lt"))
         return LLVMBuildICmp(builder, LLVMIntSLT, args[0], args[1], "");
      else if (icmp(builtin, "gt"))
         return LLVMBuildICmp(builder, LLVMIntSGT, args[0], args[1], "");
      else if (icmp(builtin, "leq"))
         return LLVMBuildICmp(builder, LLVMIntSLE, args[0], args[1], "");
      else if (icmp(builtin, "geq"))
         return LLVMBuildICmp(builder, LLVMIntSGE, args[0], args[1], "");
      else if (icmp(builtin, "neg"))
         return LLVMBuildNeg(builder, args[0], "");
      else if (icmp(builtin, "not"))
         return LLVMBuildNot(builder, args[0], "");
      else if (icmp(builtin, "and"))
         return LLVMBuildAnd(builder, args[0], args[1], "");
      else if (icmp(builtin, "or"))
         return LLVMBuildOr(builder, args[0], args[1], "");
      else if (icmp(builtin, "xor"))
         return LLVMBuildXor(builder, args[0], args[1], "");
      else if (icmp(builtin, "xnor"))
         return LLVMBuildNot(builder,
                             LLVMBuildXor(builder, args[0], args[1], ""), "");
      else if (icmp(builtin, "mod"))
         return LLVMBuildURem(builder, args[0], args[1], "");
      else if (icmp(builtin, "rem"))
         return LLVMBuildSRem(builder, args[0], args[1], "");
      else if (icmp(builtin, "exp"))
         return LLVMBuildCall(builder, llvm_fn("_iexp"), args, 2, "");
      else if (icmp(builtin, "abs")) {
         return LLVMBuildSelect(
            builder,
            LLVMBuildICmp(builder, LLVMIntSLT, args[0], llvm_int32(0), ""),
            LLVMBuildNeg(builder, args[0], ""),
            args[0], "abs");
      }
      else if (icmp(builtin, "aeq"))
         return cgen_array_rel(args[0], args[1], arg_type,
                               tree_type(tree_param(t, 1).value),
                               LLVMIntEQ, ctx);
      else if (icmp(builtin, "aneq"))
         return cgen_array_rel(args[0], args[1], arg_type,
                               tree_type(tree_param(t, 1).value),
                               LLVMIntNE, ctx);
      else if (icmp(builtin, "image")) {
         bool is_signed = (type_kind(type_base_recur(arg_type)) == T_INTEGER);
         LLVMOpcode op = (is_signed ? LLVMSExt : LLVMZExt);
         LLVMValueRef res = LLVMBuildAlloca(builder,
                                            llvm_uarray_type(LLVMInt8Type()),
                                            "image");
         LLVMValueRef iargs[] = {
            LLVMBuildCast(builder, op, args[0], LLVMInt64Type(), ""),
            llvm_int32(tree_index(tree_param(t, 0).value)),
            LLVMBuildPointerCast(builder, mod_name,
                                 LLVMPointerType(LLVMInt8Type(), 0), ""),
            res
         };
         LLVMBuildCall(builder, llvm_fn("_image"), iargs, ARRAY_LEN(iargs), "");
         return LLVMBuildLoad(builder, res, "");
      }
      else if (icmp(builtin, "succ")) {
         return LLVMBuildAdd(builder, args[0],
                             LLVMConstInt(llvm_type(arg_type), 1, false), "");
      }
      else if (icmp(builtin, "pred")) {
         return LLVMBuildAdd(builder, args[0],
                             LLVMConstInt(llvm_type(arg_type), -1, false), "");
      }
      else if (icmp(builtin, "leftof")) {
         range_t r = type_dim(tree_type(t), 0);
         int dir = (r.kind == RANGE_TO ? -1 : 1);
         return LLVMBuildAdd(builder, args[0],
                             LLVMConstInt(llvm_type(arg_type), dir, false), "");
      }
      else if (icmp(builtin, "rightof")) {
         range_t r = type_dim(tree_type(t), 0);
         int dir = (r.kind == RANGE_TO ? 1 : -1);
         return LLVMBuildAdd(builder, args[0],
                             LLVMConstInt(llvm_type(arg_type), dir, false), "");
      }
      else if (icmp(builtin, "length")) {
         assert(!cgen_const_bounds(arg_type));
         return cgen_array_len(arg_type, args[0]);
      }
      else if (icmp(builtin, "uarray_left")) {
         return LLVMBuildExtractValue(builder, args[0], 1, "left");
      }
      else if (icmp(builtin, "uarray_right")) {
         return LLVMBuildExtractValue(builder, args[0], 2, "right");
      }
      else if (icmp(builtin, "uarray_asc")) {
         return cgen_uarray_asc(args[0]);
      }
      else if (icmp(builtin, "uarray_dircmp")) {
         LLVMValueRef dir_eq = LLVMBuildICmp(
            builder, LLVMIntEQ,
            LLVMBuildExtractValue(builder, args[0], 3, "dir"),
            LLVMBuildIntCast(builder, args[1], LLVMInt8Type(), ""),
            "diff_eq");
         LLVMValueRef neg = LLVMBuildNeg(builder, args[2], "neg");
         return LLVMBuildSelect(builder, dir_eq, args[2], neg, "dirmul");
      }
      else if (icmp(builtin, "uarray_low")) {
         return LLVMBuildSelect(
            builder, cgen_uarray_asc(args[0]),
            LLVMBuildExtractValue(builder, args[0], 1, "left"),
            LLVMBuildExtractValue(builder, args[0], 2, "right"),
            "low");
      }
      else if (icmp(builtin, "uarray_high")) {
         return LLVMBuildSelect(
            builder, cgen_uarray_asc(args[0]),
            LLVMBuildExtractValue(builder, args[0], 2, "right"),
            LLVMBuildExtractValue(builder, args[0], 1, "left"),
            "high");
      }
      else if (icmp(builtin, "alt"))
         return cgen_array_rel(args[0], args[1], arg_type,
                               tree_type(tree_param(t, 1).value),
                               LLVMIntSLT, ctx);
      else if (icmp(builtin, "agt"))
         return cgen_array_rel(args[0], args[1], arg_type,
                               tree_type(tree_param(t, 1).value),
                               LLVMIntSGT, ctx);
      else if (icmp(builtin, "aleq"))
         return cgen_array_rel(args[0], args[1], arg_type,
                               tree_type(tree_param(t, 1).value),
                               LLVMIntSLE, ctx);
      else if (icmp(builtin, "ageq"))
         return cgen_array_rel(args[0], args[1], arg_type,
                               tree_type(tree_param(t, 1).value),
                               LLVMIntSGE, ctx);
      else
         fatal("cannot generate code for builtin %s", istr(builtin));
   }
   else {
      return LLVMBuildCall(builder, cgen_fdecl(decl),
                           args, tree_params(t), "");
   }
}

static LLVMValueRef cgen_scalar_signal_ref(tree_t decl, struct cgen_ctx *ctx)
{
   LLVMValueRef signal = tree_attr_ptr(decl, sig_struct_i);
   LLVMValueRef ptr =
      LLVMBuildStructGEP(builder, signal, SIGNAL_RESOLVED, "");
   LLVMValueRef deref = LLVMBuildLoad(builder, ptr, "");
   return LLVMBuildIntCast(builder, deref,
                           llvm_type(tree_type(decl)), "");
}

static LLVMValueRef cgen_ref(tree_t t, struct cgen_ctx *ctx)
{
   tree_t decl = tree_ref(t);

   switch (tree_kind(decl)) {
   case T_CONST_DECL:
      return cgen_expr(tree_value(decl), ctx);

   case T_ENUM_LIT:
      return LLVMConstInt(llvm_type(tree_type(t)), tree_pos(decl), false);

   case T_VAR_DECL:
      {
         LLVMValueRef ptr = cgen_get_var(decl, ctx);
         if (type_is_array(tree_type(decl)))
            return ptr;
         else
            return LLVMBuildLoad(builder, ptr, "");
      }

   case T_PORT_DECL:
   case T_SIGNAL_DECL:
      if (cgen_get_class(decl) == C_SIGNAL) {
         if (type_kind(tree_type(decl)) == T_CARRAY) {
            type_t type = tree_type(decl);
            return cgen_array_signal_ref(decl, type, ctx, false);
         }
         else
            return cgen_scalar_signal_ref(decl, ctx);
      }
      else
         return cgen_get_var(decl, ctx);

   default:
      assert(false);
   }
}

static LLVMValueRef cgen_array_data_ptr(type_t type, LLVMValueRef var)
{
   if (!cgen_const_bounds(type)) {
      // Unwrap array to get data pointer
      // TODO: insert bounds checking here
      return LLVMBuildExtractValue(builder, var, 0, "aptr");
   }
   else {
      LLVMValueRef indexes[] = { llvm_int32(0) };
      return LLVMBuildPointerCast(
         builder,
         LLVMBuildGEP(builder, var,
                      indexes, ARRAY_LEN(indexes), ""),
         LLVMPointerType(llvm_type(type_elem(type)), 0), "aptr");
   }
}

static LLVMValueRef cgen_array_ref(tree_t t, struct cgen_ctx *ctx)
{
   tree_t decl;
   type_t type;
   LLVMValueRef array;
   class_t class;
   LLVMValueRef idx;
   unsigned i;

   assert(tree_kind(tree_value(t)) == T_REF);

   decl = tree_ref(tree_value(t));
   type = tree_type(decl);

   array = NULL;
   class = cgen_get_class(decl);

   if (class == C_VARIABLE || class == C_CONSTANT || class == C_DEFAULT)
      array = cgen_get_var(decl, ctx);

   idx = llvm_int32(0);
   for (i = 0; i < tree_params(t); i++) {
      param_t p;
      LLVMValueRef offset;

      p = tree_param(t, i);
      assert(p.kind == P_POS);
      offset = cgen_expr(p.value, ctx);

      if (i > 0) {
         range_t r;
         int64_t low, high;
         LLVMValueRef stride;

         r = type_dim(type, i - 1);
         range_bounds(r, &low, &high);

         stride = llvm_int32(high - low + 1);
         idx = LLVMBuildMul(builder, idx, stride, "");
      }

      idx = LLVMBuildAdd(builder, idx,
                         cgen_array_off(offset, array, type, ctx, 0), "idx");
   }

   switch (class) {
   case C_VARIABLE:
   case C_CONSTANT:
   case C_DEFAULT:
      {
         LLVMValueRef data = cgen_array_data_ptr(type, array);
         LLVMValueRef ptr = LLVMBuildGEP(builder, data, &idx, 1, "");
         return LLVMBuildLoad(builder, ptr, "");
      }

   case C_SIGNAL:
      {
         LLVMValueRef signal_array = tree_attr_ptr(decl, sig_struct_i);
         LLVMValueRef indexes[] = { llvm_int32(0), idx };
         LLVMValueRef signal = LLVMBuildGEP(builder, signal_array,
                                            indexes, ARRAY_LEN(indexes), "");
         LLVMValueRef ptr =
            LLVMBuildStructGEP(builder, signal, SIGNAL_RESOLVED, "");
         LLVMValueRef deref = LLVMBuildLoad(builder, ptr, "");
         return LLVMBuildIntCast(builder, deref,
                                 llvm_type(tree_type(t)), "");
      }

   default:
      assert(false);
   }
}

static LLVMValueRef cgen_array_slice(tree_t t, struct cgen_ctx *ctx)
{
   tree_t decl;

   assert(tree_kind(tree_value(t)) == T_REF);

   decl = tree_ref(tree_value(t));

   switch (cgen_get_class(decl)) {
   case C_VARIABLE:
   case C_DEFAULT:
      {
         type_t type = tree_type(decl);
         LLVMValueRef array = cgen_get_var(decl, ctx);
         return cgen_get_slice(array, type, tree_range(t), ctx);
      }

   case C_SIGNAL:
      return cgen_array_signal_ref(decl, tree_type(t), ctx, false);

   default:
      assert(false);
   }
}

static void cgen_copy_vals(LLVMValueRef *dst, LLVMValueRef *src,
                           unsigned n, bool backwards)
{
   while (n--) {
      *dst = *src;
      ++src;
      dst += (backwards ? -1 : 1);
   }
}

static LLVMValueRef *cgen_const_aggregate(tree_t t, struct cgen_ctx *ctx,
                                          unsigned dim, unsigned *n_elems)
{
   type_t type;
   unsigned i;
   LLVMValueRef *vals;

   type = tree_type(t);

   *n_elems = 1;
   for (i = dim; i < type_dims(type); i++) {
      range_t r = type_dim(type, i);

      int64_t low, high;
      range_bounds(r, &low, &high);

      if (high < low)
         *n_elems = 0;
      else
         *n_elems *= (high - low + 1);
   }

   if (*n_elems == 0)
      return NULL;

   vals = xmalloc(*n_elems * sizeof(LLVMValueRef));

   for (i = 0; i < *n_elems; i++)
      vals[i] = NULL;

   for (i = 0; i < tree_assocs(t); i++) {
      assoc_t a;
      LLVMValueRef *sub;
      unsigned nsub;
      range_t r;
      int64_t low, high;

      a = tree_assoc(t, i);

      if (dim < type_dims(type) - 1)
         sub = cgen_const_aggregate(a.value, ctx, 0 /* XXX */, &nsub);
      else if (tree_kind(a.value) == T_AGGREGATE) {
         unsigned nvals;
         LLVMValueRef *v = cgen_const_aggregate(a.value, ctx, 0, &nvals);
         LLVMTypeRef ltype = llvm_type(type_elem(tree_type(a.value)));

         sub  = xmalloc(sizeof(LLVMValueRef));
         *sub = LLVMConstArray(ltype, v, nvals);
         nsub = 1;
      }
      else {
         sub  = xmalloc(sizeof(LLVMValueRef));
         *sub = cgen_expr(a.value, ctx);
         nsub = 1;
      }

      r = type_dim(type, dim);

      range_bounds(r, &low, &high);

      switch (a.kind) {
      case A_POS:
         if (r.kind == RANGE_TO)
            cgen_copy_vals(vals + (i * nsub), sub, nsub, false);
         else
            cgen_copy_vals(vals + ((*n_elems - i - 1) * nsub),
                           sub, nsub, true);
         break;

      case A_NAMED:
         cgen_copy_vals(vals + ((assume_int(a.name) - low) * nsub),
                        sub, nsub, false);
         break;

      case A_OTHERS:
         {
            unsigned j;
            assert((*n_elems % nsub) == 0);
            for (j = 0; j < (*n_elems / nsub); j++) {
               if (vals[j * nsub] == NULL)
                  cgen_copy_vals(vals + (j * nsub), sub, nsub, false);
            }
         }
         break;

      case A_RANGE:
         {
            int j;
            int64_t r_low, r_high;
            range_bounds(a.range, &r_low, &r_high);

            for (j = r_low; j <= r_high; j++)
               cgen_copy_vals(vals + ((j - low) * nsub), sub, nsub, false);
         }
         break;
      }

      free(sub);
   }

   for (i = 0; i < *n_elems; i++)
      assert(vals[i] != NULL);

   return vals;
}

static LLVMValueRef cgen_dyn_aggregate(tree_t t, struct cgen_ctx *ctx)
{
   type_t type;
   LLVMBasicBlockRef test_bb, body_bb, exit_bb;
   LLVMValueRef a, i, data, len, def;
   unsigned j;
   LLVMValueRef i_loaded, ge;
   LLVMValueRef what;
   LLVMValueRef indexes[1], ptr, inc;

   // Generate code to fill in the aggregate at run time

   type = tree_type(t);

   test_bb  = LLVMAppendBasicBlock(ctx->fn, "da_test");
   body_bb  = LLVMAppendBasicBlock(ctx->fn, "da_body");
   exit_bb  = LLVMAppendBasicBlock(ctx->fn, "da_exit");

   // Prelude
   a = cgen_tmp_var(t, ctx);
   i = LLVMBuildAlloca(builder, LLVMInt32Type(), "i");
   LLVMBuildStore(builder, llvm_int32(0), i);

   data = cgen_array_data_ptr(type, a);
   len = cgen_array_len(type, a);

   def = NULL;
   for (j = 0; j < tree_assocs(t); j++) {
      assoc_t a = tree_assoc(t, j);
      if (a.kind == A_OTHERS) {
         def = cgen_expr(a.value, ctx);
         break;
      }
   }

   LLVMBuildBr(builder, test_bb);

   if (def == NULL)
      def = LLVMGetUndef(llvm_type(type_elem(type)));

   // Loop test
   LLVMPositionBuilderAtEnd(builder, test_bb);
   i_loaded = LLVMBuildLoad(builder, i, "i");
   ge = LLVMBuildICmp(builder, LLVMIntUGE, i_loaded,
                                   len, "ge");
   LLVMBuildCondBr(builder, ge, exit_bb, body_bb);

   // Loop body
   LLVMPositionBuilderAtEnd(builder, body_bb);

   what = def;
   for (j = 0; j < tree_assocs(t); j++) {
      assoc_t a = tree_assoc(t, j);
      switch (a.kind) {
      case A_POS:
         {
            LLVMValueRef eq = LLVMBuildICmp(builder, LLVMIntEQ, i_loaded,
                                            llvm_int32(a.pos), "");
            what = LLVMBuildSelect(builder, eq, cgen_expr(a.value, ctx),
                                   what, "");
         }
         break;

      case A_NAMED:
         {
            LLVMValueRef eq = LLVMBuildICmp(builder, LLVMIntEQ, i_loaded,
                                            cgen_expr(a.name, ctx), "");
            what = LLVMBuildSelect(builder, eq, cgen_expr(a.value, ctx),
                                   what, "");
         }
         break;

      case A_RANGE:
         {
            LLVMIntPredicate lpred =
               (a.range.kind == RANGE_TO ? LLVMIntSGE : LLVMIntSLE);
            LLVMIntPredicate rpred =
               (a.range.kind == RANGE_TO ? LLVMIntSLE : LLVMIntSGE);

            LLVMValueRef lcmp =
               LLVMBuildICmp(builder, lpred, i_loaded,
                             cgen_expr(a.range.left, ctx), "lcmp");
            LLVMValueRef rcmp =
               LLVMBuildICmp(builder, rpred, i_loaded,
                             cgen_expr(a.range.right, ctx), "rcmp");
            LLVMValueRef in = LLVMBuildOr(builder, lcmp, rcmp, "in");

            what = LLVMBuildSelect(builder, in, cgen_expr(a.value, ctx),
                                   what, "");
         }
         break;

      case A_OTHERS:
         break;
      }
   }

   indexes[0] = i_loaded;
   ptr = LLVMBuildGEP(builder, data, indexes, ARRAY_LEN(indexes), "ptr");
   LLVMBuildStore(builder, what, ptr);

   inc = LLVMBuildAdd(builder, i_loaded, llvm_int32(1), "inc");
   LLVMBuildStore(builder, inc, i);
   LLVMBuildBr(builder, test_bb);

   // Epilogue
   LLVMPositionBuilderAtEnd(builder, exit_bb);

   return a;
}

static LLVMValueRef cgen_aggregate(tree_t t, struct cgen_ctx *ctx)
{
   bool is_const = (cgen_const_bounds(tree_type(t))
                    && cgen_is_const(t));

   if (is_const) {
      unsigned nvals;
      LLVMValueRef *vals = cgen_const_aggregate(t, ctx, 0, &nvals);

      LLVMTypeRef ltype = llvm_type(type_elem(tree_type(t)));

      LLVMTypeRef at = LLVMArrayType(ltype, nvals);
      LLVMValueRef g = LLVMAddGlobal(module, at, "");
      LLVMSetGlobalConstant(g, true);
      LLVMSetLinkage(g, LLVMInternalLinkage);
      LLVMSetInitializer(g, LLVMConstArray(ltype, vals, nvals));

      free(vals);
      return g;
   }
   else
      return cgen_dyn_aggregate(t, ctx);
}

static LLVMValueRef cgen_concat(tree_t t, struct cgen_ctx *ctx)
{
   LLVMValueRef var = cgen_tmp_var(t, ctx);
   tree_t args[2];
   LLVMValueRef args_ll[2];
   LLVMValueRef off;
   type_t type;

   assert(tree_params(t) == 2);
   args[0] = tree_param(t, 0).value;
   args[1] = tree_param(t, 1).value;

   args_ll[0] = cgen_expr(args[0], ctx);
   args_ll[1] = cgen_expr(args[1], ctx);

   off = NULL;
   type = tree_type(t);

   if (type_is_array(tree_type(args[0]))) {
      cgen_array_copy(tree_type(args[0]), type, args_ll[0], var, NULL);
      off = cgen_array_len(tree_type(args[0]), args_ll[0]);
   }
   else {
      LLVMValueRef zero = llvm_int32(0);
      LLVMValueRef data = cgen_array_data_ptr(type, var);
      LLVMValueRef ptr = LLVMBuildGEP(builder, data, &zero, 1, "");
      LLVMBuildStore(builder, args_ll[0], ptr);

      off = llvm_int32(1);
   }

   if (type_is_array(tree_type(args[1])))
      cgen_array_copy(tree_type(args[1]), type, args_ll[1], var, off);
   else {
      LLVMValueRef data = cgen_array_data_ptr(type, var);
      LLVMValueRef ptr = LLVMBuildGEP(builder, data, &off, 1, "");
      LLVMBuildStore(builder, args_ll[1], ptr);
   }

   return var;
}

static LLVMValueRef cgen_type_conv(tree_t t, struct cgen_ctx *ctx)
{
   // TODO: fix this for real<->integer conversion
   return cgen_expr(tree_param(t, 0).value, ctx);
}

static LLVMValueRef cgen_expr(tree_t t, struct cgen_ctx *ctx)
{
   switch (tree_kind(t)) {
   case T_LITERAL:
      return cgen_literal(t);
   case T_FCALL:
      return cgen_fcall(t, ctx);
   case T_REF:
      return cgen_ref(t, ctx);
   case T_ARRAY_REF:
      return cgen_array_ref(t, ctx);
   case T_ARRAY_SLICE:
      return cgen_array_slice(t, ctx);
   case T_AGGREGATE:
      return cgen_aggregate(t, ctx);
   case T_QUALIFIED:
      return cgen_expr(tree_value(t), ctx);
   case T_CONCAT:
      return cgen_concat(t, ctx);
   case T_TYPE_CONV:
      return cgen_type_conv(t, ctx);
   default:
      fatal("missing cgen_expr for kind %d", tree_kind(t));
   }
}

static void cgen_sched_process(LLVMValueRef after)
{
   LLVMValueRef args[] = { after };
   LLVMBuildCall(builder, llvm_fn("_sched_process"), args, 1, "");
}

static void cgen_sched_event(tree_t on)
{
   tree_t decl;
   type_t type;
   int32_t n;
   LLVMValueRef signal, args[2];

   if (tree_kind(on) != T_REF) {
      // It is possible for constant folding to replace a signal with
      // a constant which will then appear in a sensitivity list so
      // just ignore it
      return;
   }

   decl = tree_ref(on);
   type = tree_type(decl);

   n = 1;
   if (type_kind(type) == T_CARRAY) {
      int64_t low, high;
      range_bounds(type_dim(type, 0), &low, &high);
      n = high - low + 1;
   }

   signal = tree_attr_ptr(decl, sig_struct_i);
   args[0] = llvm_void_cast(signal);
   args[1] = llvm_int32(n);
   LLVMBuildCall(builder, llvm_fn("_sched_event"),
                 args, ARRAY_LEN(args), "");
}

static void cgen_wait(tree_t t, struct cgen_ctx *ctx)
{
   unsigned i;
   struct proc_entry *it;
   LLVMValueRef state_ptr;

   if (tree_has_delay(t))
      cgen_sched_process(cgen_expr(tree_delay(t), ctx));

   for (i = 0; i < tree_triggers(t); i++)
      cgen_sched_event(tree_trigger(t, i));

   // Find the basic block to jump to when the process is next scheduled
   for (it = ctx->entry_list; it && it->wait != t; it = it->next)
      ;
   assert(it != NULL);

   state_ptr = LLVMBuildStructGEP(builder, ctx->state, 0, "");
   LLVMBuildStore(builder, llvm_int32(it->state_num), state_ptr);
   LLVMBuildRetVoid(builder);

   LLVMPositionBuilderAtEnd(builder, it->bb);
}

static LLVMValueRef cgen_lvalue(tree_t t, struct cgen_ctx *ctx)
{
   switch (tree_kind(t)) {
   case T_REF:
      return cgen_get_var(tree_ref(t), ctx);

   case T_ARRAY_REF:
      {
         type_t type;
         param_t p;
         LLVMValueRef var, idx, data;

         type = tree_type(tree_value(t));

         p = tree_param(t, 0);
         assert(p.kind == P_POS);

         var = cgen_lvalue(tree_value(t), ctx);
         idx =
            cgen_array_off(cgen_expr(p.value, ctx), var, type, ctx, 0);

         data = cgen_array_data_ptr(type, var);
         return LLVMBuildGEP(builder, data, &idx, 1, "");
      }

   case T_ARRAY_SLICE:
      {
         LLVMValueRef array = cgen_lvalue(tree_value(t), ctx);

         type_t ty = tree_type(tree_value(t));
         return cgen_get_slice(array, ty, tree_range(t), ctx);
      }

   default:
      assert(false);
   }
}

static void cgen_var_assign(tree_t t, struct cgen_ctx *ctx)
{
   LLVMValueRef rhs = cgen_expr(tree_value(t), ctx);
   type_t value_type = tree_type(tree_value(t));

   tree_t target = tree_target(t);

   LLVMValueRef lhs = cgen_lvalue(target, ctx);

   type_t ty = tree_type(target);
   if (type_is_array(ty))
      cgen_array_copy(value_type, ty, rhs, lhs, NULL);
   else
      LLVMBuildStore(builder, rhs, lhs);
}

static void cgen_sched_waveform(LLVMValueRef signal, LLVMValueRef value,
                                LLVMValueRef after)
{
   LLVMValueRef args[] = {
      llvm_void_cast(signal),
      llvm_int32(0 /* source, TODO */),
      LLVMBuildZExt(builder, value, LLVMInt64Type(), ""),
      after
   };
   LLVMBuildCall(builder, llvm_fn("_sched_waveform"),
                 args, ARRAY_LEN(args), "");
}

static void cgen_array_signal_store(tree_t decl, type_t slice_type,
                                    LLVMValueRef rhs, type_t rhs_type,
                                    LLVMValueRef after, struct cgen_ctx *ctx)
{
   type_t type;
   char name[256];
   range_t r;
   LLVMValueRef left_off, right_off;
   LLVMValueRef left_abs, right_abs;
   LLVMValueRef rhs_data;
   LLVMValueRef s_signal;
   LLVMValueRef indexes[2];
   LLVMValueRef p_signal;
   LLVMValueRef p_rhs;
   LLVMValueRef args[4];

   type = tree_type(decl);
   assert(type_kind(type) == T_CARRAY);

   snprintf(name, sizeof(name), "%s_vec_store",
            istr(type_ident(type_elem(tree_type(decl)))));

   r = type_dim(slice_type, 0);
   left_off =
      cgen_expr(r.kind == RANGE_TO ? r.left : r.right, ctx);
   right_off =
      cgen_expr(r.kind == RANGE_TO ? r.right : r.left, ctx);

   left_abs = cgen_array_off(left_off, NULL, type, ctx, 0);
   right_abs = cgen_array_off(right_off, NULL, type, ctx, 0);

   rhs_data = cgen_array_data_ptr(rhs_type, rhs);

   s_signal = tree_attr_ptr(decl, sig_struct_i);
   indexes[0] = llvm_int32(0);
   indexes[1] = llvm_int32(0);
   p_signal = LLVMBuildGEP(builder, s_signal,
                                        indexes, ARRAY_LEN(indexes), "");
   p_rhs = LLVMBuildGEP(builder, rhs_data, indexes, 1, "");

   args[0] = p_signal;
   args[1] = p_rhs;
   args[2] = left_abs;
   args[3] = right_abs;
   LLVMBuildCall(builder, llvm_fn(name), args, ARRAY_LEN(args), "");
}

static void cgen_scalar_signal_assign(tree_t t, tree_t value, LLVMValueRef rhs,
                                      LLVMValueRef after, struct cgen_ctx *ctx)
{
   tree_t decl = tree_ref(tree_target(t));
   if (type_kind(tree_type(decl)) == T_CARRAY)
      cgen_array_signal_store(decl, tree_type(decl), rhs,
                              tree_type(value), after, ctx);
   else
      cgen_sched_waveform(tree_attr_ptr(decl, sig_struct_i), rhs, after);
}

static void cgen_array_signal_assign(tree_t t, LLVMValueRef rhs,
                                     LLVMValueRef after, struct cgen_ctx *ctx)
{
   tree_t target, decl;
   param_t p;
   LLVMValueRef elem;

   target = tree_target(t);

   assert(tree_kind(tree_value(target)) == T_REF);

   decl = tree_ref(tree_value(target));
   assert(type_kind(tree_type(decl)) == T_CARRAY);

   p = tree_param(target, 0);
   assert(p.kind == P_POS);

   elem = cgen_expr(p.value, ctx);
   cgen_sched_waveform(cgen_array_signal_ptr(decl, elem), rhs, after);
}

static void cgen_slice_signal_assign(tree_t t, tree_t value, LLVMValueRef rhs,
                                     LLVMValueRef after, struct cgen_ctx *ctx)
{
   tree_t target, decl;

   target = tree_target(t);

   assert(tree_kind(tree_value(target)) == T_REF);

   decl = tree_ref(tree_value(target));
   assert(type_kind(tree_type(decl)) == T_CARRAY);

   cgen_array_signal_store(decl, tree_type(target), rhs,
                           tree_type(value), after, ctx);
}

static void cgen_signal_assign(tree_t t, struct cgen_ctx *ctx)
{
   unsigned i;

   for (i = 0; i < tree_waveforms(t); i++) {
      tree_t w = tree_waveform(t, i);

      LLVMValueRef rhs = cgen_expr(tree_value(w), ctx);
      LLVMValueRef after = (tree_has_delay(w)
                            ? cgen_expr(tree_delay(w), ctx)
                            : llvm_int64(0));

      switch (tree_kind(tree_target(t))) {
      case T_REF:
         cgen_scalar_signal_assign(t, tree_value(w), rhs, after, ctx);
         break;

      case T_ARRAY_REF:
         cgen_array_signal_assign(t, rhs, after, ctx);
         break;

      case T_ARRAY_SLICE:
         cgen_slice_signal_assign(t, tree_value(w), rhs, after, ctx);
         break;

      default:
         assert(false);
      }
   }
}

static void cgen_assert(tree_t t, struct cgen_ctx *ctx)
{
   type_t msg_type;
   LLVMValueRef args[5];

   int is_report = tree_attr_int(t, ident_new("is_report"), 0);

   LLVMValueRef message  = cgen_expr(tree_message(t), ctx);
   LLVMValueRef severity = cgen_expr(tree_severity(t), ctx);

   LLVMBasicBlockRef thenbb, elsebb = NULL;
   if (!is_report) {
      LLVMValueRef test = cgen_expr(tree_value(t), ctx);
      LLVMValueRef failed = LLVMBuildNot(builder, test, "");

      thenbb = LLVMAppendBasicBlock(ctx->fn, "assert_fail");
      elsebb = LLVMAppendBasicBlock(ctx->fn, "assert_pass");

      LLVMBuildCondBr(builder, failed, thenbb, elsebb);

      LLVMPositionBuilderAtEnd(builder, thenbb);
   }

   msg_type = tree_type(tree_message(t));

   args[0] = cgen_array_data_ptr(msg_type, message);
   args[1] = cgen_array_len(msg_type, message);
   args[2] = severity;
   args[3] = llvm_int32(tree_index(t));
   args[4] = LLVMBuildPointerCast(builder, mod_name,
                                  LLVMPointerType(LLVMInt8Type(), 0), "");
   LLVMBuildCall(builder, llvm_fn("_assert_fail"),
                 args, ARRAY_LEN(args), "");

   if (!is_report) {
      LLVMBuildBr(builder, elsebb);
      LLVMPositionBuilderAtEnd(builder, elsebb);
   }
}

static void cgen_if(tree_t t, struct cgen_ctx *ctx)
{
   unsigned i;

   LLVMBasicBlockRef then_bb = LLVMAppendBasicBlock(ctx->fn, "then");
   LLVMBasicBlockRef else_bb = LLVMAppendBasicBlock(ctx->fn, "else");

   LLVMBasicBlockRef end_bb =
      (tree_else_stmts(t) > 0)
      ? LLVMAppendBasicBlock(ctx->fn, "ifend")
      : else_bb;

   LLVMValueRef test = cgen_expr(tree_value(t), ctx);
   LLVMBuildCondBr(builder, test, then_bb, else_bb);

   LLVMPositionBuilderAtEnd(builder, then_bb);

   for (i = 0; i < tree_stmts(t); i++)
      cgen_stmt(tree_stmt(t, i), ctx);

   LLVMBuildBr(builder, end_bb);

   if (tree_else_stmts(t) > 0) {
      LLVMPositionBuilderAtEnd(builder, else_bb);

      for (i = 0; i < tree_else_stmts(t); i++)
         cgen_stmt(tree_else_stmt(t, i), ctx);

      LLVMBuildBr(builder, end_bb);
   }

   LLVMPositionBuilderAtEnd(builder, end_bb);
}

static void cgen_return(tree_t t, struct cgen_ctx *ctx)
{
   LLVMBasicBlockRef unreach_bb;
   LLVMValueRef rval = cgen_expr(tree_value(t), ctx);

   // If we are returning an array then wrap it with metadata
   type_t stype = tree_type(tree_value(t));
   if (type_is_array(stype)) {
      type_t rtype;
      LLVMTypeRef base_type, ptr_type;
      LLVMValueRef args[2], buf, rarray, values[4];

      // Need to make a copy of this array as it is currently
      // on the stack

      rtype = type_result(tree_type(ctx->fdecl));
      assert(type_kind(rtype) == T_UARRAY);

      base_type = llvm_type(type_elem(stype));

      args[0] = cgen_array_len(stype, rval);
      args[1] = llvm_sizeof(base_type);
      buf = LLVMBuildCall(builder, llvm_fn("_tmp_alloc"),
                       args, ARRAY_LEN(args), "buf");

      ptr_type = LLVMPointerType(base_type, 0);

      rarray = cgen_array_meta(
         rtype,
         cgen_array_left(stype, rval),
         cgen_array_right(stype, rval),
         cgen_array_dir(stype, rval),
         LLVMBuildPointerCast(builder, buf, ptr_type, ""));

      cgen_array_copy(stype, rtype, rval, rarray, NULL);

      values[0] = LLVMBuildExtractValue(builder, rarray, 0, "ptr");
      values[1] = LLVMBuildExtractValue(builder, rarray, 1, "left");
      values[2] = LLVMBuildExtractValue(builder, rarray, 2, "right");
      values[3] = LLVMBuildExtractValue(builder, rarray, 3, "dir");
      LLVMBuildAggregateRet(builder, values, ARRAY_LEN(values));
   }
   else
      LLVMBuildRet(builder, rval);

   unreach_bb = LLVMAppendBasicBlock(ctx->fn, "unreach");
   LLVMPositionBuilderAtEnd(builder, unreach_bb);
}

static void cgen_while(tree_t t, struct cgen_ctx *ctx)
{
   struct block_list *bl;
   unsigned i;

   LLVMBasicBlockRef body_bb = LLVMAppendBasicBlock(ctx->fn, "wbody");
   LLVMBasicBlockRef exit_bb = LLVMAppendBasicBlock(ctx->fn, "wexit");
   LLVMBasicBlockRef test_bb = LLVMAppendBasicBlock(ctx->fn, "while");

   LLVMBuildBr(builder, test_bb);
   LLVMPositionBuilderAtEnd(builder, test_bb);

   if (tree_has_value(t)) {
      LLVMValueRef test = cgen_expr(tree_value(t), ctx);
      LLVMBuildCondBr(builder, test, body_bb, exit_bb);
   }
   else
      LLVMBuildBr(builder, body_bb);

   bl = xmalloc(sizeof(struct block_list));
   bl->exit_bb = exit_bb;
   bl->name    = tree_ident(t);
   bl->next    = ctx->blocks;

   ctx->blocks = bl;

   LLVMPositionBuilderAtEnd(builder, body_bb);
   for (i = 0; i < tree_stmts(t); i++)
      cgen_stmt(tree_stmt(t, i), ctx);
   LLVMBuildBr(builder, test_bb);

   LLVMPositionBuilderAtEnd(builder, exit_bb);

   ctx->blocks = bl->next;
   free(bl);
}

static void cgen_block(tree_t t, struct cgen_ctx *ctx)
{
   unsigned i;
   for (i = 0; i < tree_stmts(t); i++)
      cgen_stmt(tree_stmt(t, i), ctx);
}

static void cgen_exit(tree_t t, struct cgen_ctx *ctx)
{
   struct block_list *bl;

   LLVMBasicBlockRef not_bb = LLVMAppendBasicBlock(ctx->fn, "not_exit");

   if (tree_has_value(t)) {
      LLVMBasicBlockRef exit_bb = LLVMAppendBasicBlock(ctx->fn, "exit");
      LLVMValueRef test = cgen_expr(tree_value(t), ctx);
      LLVMBuildCondBr(builder, test, exit_bb, not_bb);
      LLVMPositionBuilderAtEnd(builder, exit_bb);
   }

   // TODO: check ident2 -> if NULL then most closely nested block
   // else search through block_list

   assert(ctx->blocks != NULL);

   bl = ctx->blocks;

   LLVMBuildBr(builder, bl->exit_bb);

   LLVMPositionBuilderAtEnd(builder, not_bb);
}

static void cgen_case_scalar(tree_t t, struct cgen_ctx *ctx)
{
   // Case with scalar value maps onto LLVM case

   LLVMBasicBlockRef exit_bb = LLVMAppendBasicBlock(ctx->fn, "case_exit");
   LLVMBasicBlockRef else_bb = exit_bb;
   unsigned num_cases = 0;
   unsigned i;
   LLVMValueRef val, sw;

   for (i = 0; i < tree_assocs(t); i++) {
      if (tree_assoc(t, i).kind == A_OTHERS)
         else_bb = LLVMAppendBasicBlock(ctx->fn, "case_others");
      else
         num_cases++;
   }

   val = cgen_expr(tree_value(t), ctx);
   sw = LLVMBuildSwitch(builder, val, else_bb, num_cases);

   for (i = 0; i < tree_assocs(t); i++) {
      assoc_t a = tree_assoc(t, i);
      switch (a.kind) {
      case A_NAMED:
         {
            LLVMBasicBlockRef bb = LLVMAppendBasicBlock(ctx->fn, "");
            LLVMAddCase(sw, cgen_expr(a.name, ctx), bb);

            LLVMPositionBuilderAtEnd(builder, bb);
         }
         break;

      case A_OTHERS:
         LLVMPositionBuilderAtEnd(builder, else_bb);
         break;

      default:
         assert(false);
      }

      cgen_stmt(a.value, ctx);
      LLVMBuildBr(builder, exit_bb);
   }

   LLVMPositionBuilderAtEnd(builder, exit_bb);
}

static void cgen_case_array(tree_t t, struct cgen_ctx *ctx)
{
   // Case with array value must use chain of ifs

   // TODO: multiple calls to cgen_array_rel is very inefficient
   //       replace this with code to compare all values in a single
   //       loop (e.g. build a bit mask of length #assocs)

   LLVMBasicBlockRef exit_bb = LLVMAppendBasicBlock(ctx->fn, "case_exit");

   LLVMValueRef val = cgen_expr(tree_value(t), ctx);
   type_t type = tree_type(tree_value(t));

   bool have_others = false;
   unsigned i;
   for (i = 0; i < tree_assocs(t); i++) {
      LLVMBasicBlockRef next_bb = NULL;
      assoc_t a = tree_assoc(t, i);
      switch (a.kind) {
      case A_NAMED:
         {
            LLVMValueRef eq;
            LLVMBasicBlockRef this_bb =
               LLVMAppendBasicBlock(ctx->fn, "case_body");
            next_bb = LLVMAppendBasicBlock(ctx->fn, "case_test");
            eq = cgen_array_rel(val, cgen_expr(a.name, ctx),
                                type, type, LLVMIntEQ, ctx);
            LLVMBuildCondBr(builder, eq, this_bb, next_bb);
            LLVMPositionBuilderAtEnd(builder, this_bb);
         }
         break;

      case A_OTHERS:
         next_bb = exit_bb;
         have_others = true;
         break;

      default:
         assert(false);
      }

      cgen_stmt(a.value, ctx);
      LLVMBuildBr(builder, exit_bb);

      LLVMPositionBuilderAtEnd(builder, next_bb);
   }

   if (!have_others)
      LLVMBuildBr(builder, exit_bb);

   LLVMPositionBuilderAtEnd(builder, exit_bb);
}

static void cgen_case(tree_t t, struct cgen_ctx *ctx)
{
   if (type_is_array(tree_type(tree_value(t))))
      cgen_case_array(t, ctx);
   else
      cgen_case_scalar(t, ctx);
}

static void cgen_pcall(tree_t t, struct cgen_ctx *ctx)
{
   tree_t decl = tree_ref(t);

   LLVMValueRef args[tree_params(t)];
   cgen_call_args(t, args, ctx);

   LLVMBuildCall(builder, cgen_pdecl(decl), args, tree_params(t), "");
}

static void cgen_stmt(tree_t t, struct cgen_ctx *ctx)
{
   switch (tree_kind(t)) {
   case T_WAIT:
      cgen_wait(t, ctx);
      break;
   case T_VAR_ASSIGN:
      cgen_var_assign(t, ctx);
      break;
   case T_SIGNAL_ASSIGN:
      cgen_signal_assign(t, ctx);
      break;
   case T_ASSERT:
      cgen_assert(t, ctx);
      break;
   case T_IF:
      cgen_if(t, ctx);
      break;
   case T_RETURN:
      cgen_return(t, ctx);
      break;
   case T_WHILE:
      cgen_while(t, ctx);
      break;
   case T_BLOCK:
      cgen_block(t, ctx);
      break;
   case T_EXIT:
      cgen_exit(t, ctx);
      break;
   case T_CASE:
      cgen_case(t, ctx);
      break;
   case T_PCALL:
      cgen_pcall(t, ctx);
      break;
   default:
      assert(false);
   }
}

static void cgen_jump_table_fn(tree_t t, void *arg)
{
   struct cgen_ctx *ctx;
   struct proc_entry *p;

   assert(tree_kind(t) == T_WAIT);

   ctx = arg;

   p = xmalloc(sizeof(struct proc_entry));
   p->next = NULL;
   p->wait = t;
   p->bb   = NULL;

   if (ctx->entry_list == NULL) {
      p->state_num = 1;
      ctx->entry_list = p;
   }
   else {
      struct proc_entry *it;
      for (it = ctx->entry_list; it->next != NULL; it = it->next)
         ;
      p->state_num = it->state_num + 1;
      it->next = p;
   }
}

static void cgen_driver_init_fn(tree_t t, void *arg)
{
   struct cgen_ctx *ctx;
   tree_t target;
   tree_kind_t kind;
   tree_t decl;
   ident_t tag_i;
   LLVMValueRef val;
   type_t type;

   assert(tree_kind(t) == T_SIGNAL_ASSIGN);

   ctx = arg;

   target = tree_target(t);
   while ((kind = tree_kind(target)) != T_REF) {
      assert((kind == T_ARRAY_REF) || (kind == T_ARRAY_SLICE));
      target = tree_value(target);
   }

   decl = tree_ref(target);
   assert(tree_kind(decl) == T_SIGNAL_DECL);

   tag_i = ident_new("driver_tag");
   if (tree_attr_ptr(decl, tag_i) == ctx->proc)
      return;   // Already initialised this signal

   assert(tree_has_value(decl));
   val = cgen_expr(tree_value(decl), ctx);

   type = tree_type(decl);
   if (type_kind(type) == T_CARRAY) {
      // Initialise only those sub-elements for which this
      // process is a driver

      unsigned i, j;
      int64_t low, high;
      range_bounds(type_dim(type, 0), &low, &high);

      for (i = 0; i < high - low + 1; i++) {
         for (j = 0; j < tree_sub_drivers(decl, i); j++) {
            if (tree_sub_driver(decl, i, j) == ctx->proc) {
               LLVMValueRef ptr = cgen_array_signal_ptr(decl, llvm_int32(i));
               LLVMValueRef indices[] = { llvm_int32(0), llvm_int32(i) };
               LLVMValueRef ith = LLVMBuildGEP(builder, val, indices,
                                               ARRAY_LEN(indices), "");
               LLVMValueRef deref = LLVMBuildLoad(builder, ith, "");
               cgen_sched_waveform(ptr, deref, llvm_int64(0));
            }
         }
      }
   }
   else
      cgen_sched_waveform(tree_attr_ptr(decl, sig_struct_i), val,
                          llvm_int64(0));

   tree_add_attr_ptr(decl, tag_i, ctx->proc);
}

struct cgen_proc_var_ctx {
   LLVMTypeRef *types;
   unsigned    offset;
};

static void cgen_visit_proc_vars(tree_t t, void *context)
{
   struct cgen_proc_var_ctx *ctx = context;

   ctx->types[ctx->offset] = llvm_type(tree_type(t));
   tree_add_attr_int(t, var_offset_i, ctx->offset);

   ctx->offset++;
}

static LLVMTypeRef cgen_process_state_type(tree_t t)
{
   struct cgen_proc_var_ctx ctx;
   char name[64];
   LLVMTypeRef ty;

   unsigned nvars = tree_visit_only(t, NULL, NULL, T_VAR_DECL);

   LLVMTypeRef fields[nvars + 1];
   fields[0] = LLVMInt32Type();   // State

   ctx.types  = fields;
   ctx.offset = 1;
   tree_visit_only(t, cgen_visit_proc_vars, &ctx, T_VAR_DECL);

   snprintf(name, sizeof(name), "%s__state_s", istr(tree_ident(t)));
   ty = LLVMStructCreateNamed(LLVMGetGlobalContext(), name);
   if (ty == NULL)
      fatal("failed to add type name %s", name);
   LLVMStructSetBody(ty, fields, ARRAY_LEN(fields), false);

   return ty;
}

static void cgen_process(tree_t t)
{
   struct cgen_ctx ctx;
   char state_name[64];
   LLVMTypeRef state_ty;
   LLVMTypeRef pargs[1], ftype;
   LLVMBasicBlockRef entry_bb, jt_bb, init_bb, start_bb;
   LLVMValueRef param, reset;
   LLVMValueRef state_ptr, jtarget, jswitch;
   struct proc_entry *it;
   unsigned i;

   assert(tree_kind(t) == T_PROCESS);

   ctx.entry_list = NULL;
   ctx.proc       = t;

   // Create a global structure to hold process state
   snprintf(state_name, sizeof(state_name),
            "%s__state", istr(tree_ident(t)));
   state_ty = cgen_process_state_type(t);
   ctx.state = LLVMAddGlobal(module, state_ty, state_name);
   LLVMSetLinkage(ctx.state, LLVMInternalLinkage);

   // Process state is initially undefined: call process function
   // with non-zero argument to initialise
   LLVMSetInitializer(ctx.state, LLVMGetUndef(state_ty));

   pargs[0] = LLVMInt32Type();
   ftype = LLVMFunctionType(LLVMVoidType(), pargs, 1, false);
   ctx.fn = LLVMAddFunction(module, istr(tree_ident(t)), ftype);

   entry_bb = LLVMAppendBasicBlock(ctx.fn, "entry");
   jt_bb    = LLVMAppendBasicBlock(ctx.fn, "jump_table");
   init_bb  = LLVMAppendBasicBlock(ctx.fn, "init");
   start_bb = LLVMAppendBasicBlock(ctx.fn, "start");

   LLVMPositionBuilderAtEnd(builder, entry_bb);

   // If the parameter is non-zero jump to the init block

   param = LLVMGetParam(ctx.fn, 0);
   reset =
      LLVMBuildICmp(builder, LLVMIntNE, param, llvm_int32(0), "");
   LLVMBuildCondBr(builder, reset, init_bb, jt_bb);

   // Generate the jump table at the start of a process to handle
   // resuming from a wait statement

   LLVMPositionBuilderAtEnd(builder, jt_bb);

   tree_visit_only(t, cgen_jump_table_fn, &ctx, T_WAIT);

   if (ctx.entry_list == NULL)
      warn_at(tree_loc(t), "no wait statement in process");

   state_ptr = LLVMBuildStructGEP(builder, ctx.state, 0, "");
   jtarget = LLVMBuildLoad(builder, state_ptr, "");

   // TODO: if none of the cases match should jump to unreachable
   // block rather than init
   jswitch = LLVMBuildSwitch(builder, jtarget, init_bb, 10);

   LLVMAddCase(jswitch, llvm_int32(0), start_bb);

   for (it = ctx.entry_list; it != NULL; it = it->next) {
      it->bb = LLVMAppendBasicBlock(ctx.fn, istr(tree_ident(it->wait)));

      LLVMAddCase(jswitch, llvm_int32(it->state_num), it->bb);
   }

   LLVMPositionBuilderAtEnd(builder, init_bb);

   // Variable initialisation

   for (i = 0; i < tree_decls(t); i++) {
      tree_t v = tree_decl(t, i);
      if (tree_kind(v) == T_VAR_DECL) {
         LLVMValueRef val, var_ptr;
         type_t ty;

         assert(tree_has_value(v));
         val = cgen_expr(tree_value(v), &ctx);

         var_ptr = cgen_get_var(v, &ctx);

         ty = tree_type(v);
         if (type_is_array(ty))
            cgen_array_copy(ty, ty, val, var_ptr, NULL);
         else
            LLVMBuildStore(builder, val, var_ptr);
      }
   }

   // Signal driver initialisation

   tree_visit_only(t, cgen_driver_init_fn, &ctx, T_SIGNAL_ASSIGN);

   // Return to simulation kernel after initialisation

   cgen_sched_process(llvm_int64(0));
   LLVMBuildStore(builder, llvm_int32(0 /* start */), state_ptr);
   LLVMBuildRetVoid(builder);

   // Sequential statements

   LLVMPositionBuilderAtEnd(builder, start_bb);

   for (i = 0; i < tree_stmts(t); i++)
      cgen_stmt(tree_stmt(t, i), &ctx);

   LLVMBuildBr(builder, start_bb);

   // Free context memory

   while (ctx.entry_list != NULL) {
      struct proc_entry *next = ctx.entry_list->next;
      free(ctx.entry_list);
      ctx.entry_list = next;
   }
}

static LLVMTypeRef cgen_signal_type(void)
{
   LLVMTypeRef ty = LLVMGetTypeByName(module, "signal_s");
   if (ty == NULL) {
      LLVMTypeRef fields[SIGNAL_N_FIELDS];
      fields[SIGNAL_RESOLVED]   = LLVMInt64Type();
      fields[SIGNAL_LAST_VALUE] = LLVMInt64Type();
      fields[SIGNAL_DECL]       = llvm_void_ptr();
      fields[SIGNAL_FLAGS]      = LLVMInt8Type();
      fields[SIGNAL_N_SOURCES]  = LLVMInt8Type();
      fields[SIGNAL_OFFSET]     = LLVMInt16Type();
      fields[SIGNAL_SOURCES]    = llvm_void_ptr();
      fields[SIGNAL_SENSITIVE]  = llvm_void_ptr();
      fields[SIGNAL_EVENT_CB]   = llvm_void_ptr();

      if (!(ty = LLVMStructCreateNamed(LLVMGetGlobalContext(), "signal_s")))
         fatal("failed to add type name signal_s");
      LLVMStructSetBody(ty, fields, ARRAY_LEN(fields), false);
   }

   return ty;
}

static LLVMValueRef cgen_signal_init(void)
{
   LLVMValueRef init[SIGNAL_N_FIELDS];
   LLVMTypeRef signal_s;

   init[SIGNAL_RESOLVED]   = llvm_int64(0);
   init[SIGNAL_LAST_VALUE] = llvm_int64(0);
   init[SIGNAL_DECL]       = LLVMConstNull(llvm_void_ptr());
   init[SIGNAL_FLAGS]      = llvm_int8(0);
   init[SIGNAL_N_SOURCES]  = llvm_int8(0);
   init[SIGNAL_OFFSET]     = LLVMConstInt(LLVMInt16Type(), 0, false);
   init[SIGNAL_SOURCES]    = LLVMConstNull(llvm_void_ptr());
   init[SIGNAL_SENSITIVE]  = LLVMConstNull(llvm_void_ptr());
   init[SIGNAL_EVENT_CB]   = LLVMConstNull(llvm_void_ptr());

   signal_s = LLVMGetTypeByName(module, "signal_s");
   assert(signal_s != NULL);

   return LLVMConstNamedStruct(signal_s, init, ARRAY_LEN(init));
}

static void cgen_scalar_signal(tree_t t)
{
   LLVMTypeRef ty = cgen_signal_type();
   LLVMValueRef v = LLVMAddGlobal(module, ty, istr(tree_ident(t)));
   LLVMSetInitializer(v, cgen_signal_init());

   tree_add_attr_ptr(t, sig_struct_i, v);
}

static void cgen_array_signal_load_fn(tree_t t, LLVMValueRef v)
{
   type_t elem_type;
   char name[256];
   LLVMValueRef fn;
   LLVMBasicBlockRef saved_bb;
   LLVMTypeRef args[5];
   LLVMBasicBlockRef entry_bb, test_bb, body_bb, norm_bb, last_bb, merge_bb, exit_bb;
   LLVMValueRef i, i_loaded, ge, index[1], signal, ptr_last, ptr_resolved, phi, values[2];
   LLVMBasicBlockRef bbs[2];
   LLVMValueRef deref, val, dst_index[1], dst, inc;

   // Build a function to load the array into a temporary

   elem_type = type_elem(tree_type(t));

   snprintf(name, sizeof(name), "%s_vec_load",
            istr(type_ident(elem_type)));

   if ((fn = LLVMGetNamedFunction(module, name)))
      return;

   saved_bb = LLVMGetInsertBlock(builder);

   args[0] = LLVMPointerType(cgen_signal_type(), 0);
   args[1] = LLVMPointerType(llvm_type(elem_type), 0);
   args[2] = LLVMInt32Type();    // Left
   args[3] = LLVMInt32Type();    // Right
   args[4] = LLVMInt1Type();     // Last value
   fn = LLVMAddFunction(module, name,
                        LLVMFunctionType(LLVMVoidType(),
                                         args, ARRAY_LEN(args), false));

   entry_bb = LLVMAppendBasicBlock(fn, "entry");
   test_bb  = LLVMAppendBasicBlock(fn, "test");
   body_bb  = LLVMAppendBasicBlock(fn, "body");
   norm_bb  = LLVMAppendBasicBlock(fn, "normal");
   last_bb  = LLVMAppendBasicBlock(fn, "last");
   merge_bb = LLVMAppendBasicBlock(fn, "merge");
   exit_bb  = LLVMAppendBasicBlock(fn, "exit");

   // Prelude
   LLVMPositionBuilderAtEnd(builder, entry_bb);
   i = LLVMBuildAlloca(builder, LLVMInt32Type(), "i");
   LLVMBuildStore(builder, LLVMGetParam(fn, 2), i);
   LLVMBuildBr(builder, test_bb);

   // Loop test
   LLVMPositionBuilderAtEnd(builder, test_bb);
   i_loaded = LLVMBuildLoad(builder, i, "");
   ge = LLVMBuildICmp(builder, LLVMIntUGE,
                      LLVMGetParam(fn, 3),
                      i_loaded, "ge");
   LLVMBuildCondBr(builder, ge, body_bb, exit_bb);

   // Loop body
   LLVMPositionBuilderAtEnd(builder, body_bb);

   index[0] = i_loaded;
   signal = LLVMBuildGEP(builder, LLVMGetParam(fn, 0),
                         index, ARRAY_LEN(index),
                         "signal");

   // Select either the current or last value

   LLVMBuildCondBr(builder, LLVMGetParam(fn, 4), last_bb, norm_bb);

   LLVMPositionBuilderAtEnd(builder, last_bb);
   ptr_last =
      LLVMBuildStructGEP(builder, signal, SIGNAL_LAST_VALUE, "last_value");
   LLVMBuildBr(builder, merge_bb);

   LLVMPositionBuilderAtEnd(builder, norm_bb);
   ptr_resolved =
      LLVMBuildStructGEP(builder, signal, SIGNAL_RESOLVED, "resolved");
   LLVMBuildBr(builder, merge_bb);

   LLVMPositionBuilderAtEnd(builder, merge_bb);
   phi = LLVMBuildPhi(builder, LLVMTypeOf(ptr_last), "ptr");

   values[0] = ptr_last;
   values[1] = ptr_resolved;
   bbs[0]    = last_bb;
   bbs[1]    = norm_bb;
   LLVMAddIncoming(phi, values, bbs, 2);

   deref = LLVMBuildLoad(builder, phi, "deref");
   val = LLVMBuildIntCast(builder, deref, llvm_type(elem_type), "val");
   dst_index[0] = LLVMBuildSub(builder, i_loaded, LLVMGetParam(fn, 2), "");
   dst = LLVMBuildGEP(builder, LLVMGetParam(fn, 1),
                      dst_index, ARRAY_LEN(dst_index),
                      "dst");
   LLVMBuildStore(builder, val, dst);

   inc =
      LLVMBuildAdd(builder, i_loaded, llvm_int32(1), "inc");
   LLVMBuildStore(builder, inc, i);
   LLVMBuildBr(builder, test_bb);

   // Epilogue
   LLVMPositionBuilderAtEnd(builder, exit_bb);
   LLVMBuildRetVoid(builder);

   LLVMPositionBuilderAtEnd(builder, saved_bb);
}

static void cgen_array_signal_store_fn(tree_t t, LLVMValueRef v)
{
   type_t elem_type;
   char name[256];
   LLVMValueRef fn;
   LLVMBasicBlockRef saved_bb;
   LLVMTypeRef ll_elem_type;
   LLVMTypeRef fn_args[4];
   LLVMBasicBlockRef entry_bb;
   LLVMValueRef n, dst_index[1], signal, src_index[1], p_src, args[6];

   // Build a function to schedule an array assignment

   elem_type = type_elem(tree_type(t));

   snprintf(name, sizeof(name), "%s_vec_store",
            istr(type_ident(elem_type)));

   if ((fn = LLVMGetNamedFunction(module, name)))
      return;

   saved_bb = LLVMGetInsertBlock(builder);

   ll_elem_type = llvm_type(elem_type);

   fn_args[0] = LLVMPointerType(cgen_signal_type(), 0);
   fn_args[1] = LLVMPointerType(ll_elem_type, 0);
   fn_args[2] = LLVMInt32Type();    // Left
   fn_args[3] = LLVMInt32Type();    // Right
   fn = LLVMAddFunction(module, name,
                        LLVMFunctionType(LLVMVoidType(),
                                         fn_args, ARRAY_LEN(fn_args),
                                         false));

   entry_bb = LLVMAppendBasicBlock(fn, "entry");
   LLVMPositionBuilderAtEnd(builder, entry_bb);

   n =
      LLVMBuildAdd(builder,
                   LLVMBuildSub(builder, LLVMGetParam(fn, 3),
                                LLVMGetParam(fn, 2), ""),
                   llvm_int32(1), "n");

   dst_index[0] = LLVMGetParam(fn, 2);
   signal = LLVMBuildGEP(builder, LLVMGetParam(fn, 0),
                         dst_index, ARRAY_LEN(dst_index),
                         "signal");

   src_index[0] = llvm_int32(0);
   p_src = LLVMBuildGEP(builder, LLVMGetParam(fn, 1),
                        src_index, ARRAY_LEN(src_index),
                        "p_src");
   args[0] = llvm_void_cast(signal);
   args[1] = llvm_int32(0 /* source, TODO */);
   args[2] = llvm_void_cast(p_src);
   args[3] = n;
   args[4] = llvm_sizeof(ll_elem_type);
   args[5] = llvm_int64(0 /* after, TODO */);
   LLVMBuildCall(builder, llvm_fn("_sched_waveform_vec"),
                 args, ARRAY_LEN(args), "");

   LLVMBuildRetVoid(builder);

   LLVMPositionBuilderAtEnd(builder, saved_bb);
}

static void cgen_array_signal(tree_t t)
{
   range_t r;
   int64_t low, high;
   unsigned n_elems;
   LLVMTypeRef base_ty, array_ty;
   LLVMValueRef v;
   LLVMValueRef *array_init;
   unsigned i;

   assert(tree_drivers(t) == 0);

   r = type_dim(tree_type(t), 0);
   range_bounds(r, &low, &high);

   n_elems = high - low + 1;

   base_ty = cgen_signal_type();
   array_ty = LLVMArrayType(base_ty, n_elems);
   v = LLVMAddGlobal(module, array_ty, istr(tree_ident(t)));

   array_init = (LLVMValueRef *)xmalloc(n_elems * sizeof(LLVMValueRef));
   for (i = 0; i < n_elems; i++)
      array_init[i] = cgen_signal_init();
   LLVMSetInitializer(v, LLVMConstArray(base_ty, array_init, n_elems));

   cgen_array_signal_load_fn(t, v);
   cgen_array_signal_store_fn(t, v);

   tree_add_attr_ptr(t, sig_struct_i, v);

   free(array_init);
}

static void cgen_signal(tree_t t)
{
   assert(tree_kind(t) == T_SIGNAL_DECL);

   if (type_kind(tree_type(t)) == T_CARRAY)
      cgen_array_signal(t);
   else
      cgen_scalar_signal(t);
}

static void cgen_func_vars(tree_t d, void *context)
{
   struct cgen_ctx *ctx = context;

   LLVMValueRef var = cgen_local_var(d, ctx);

   tree_add_attr_ptr(d, local_var_i, var);
}

static void cgen_func_body(tree_t t)
{
   type_t ftype;
   LLVMTypeRef args[tree_ports(t)];
   const char *mangled;
   LLVMValueRef fn;
   LLVMBasicBlockRef entry_bb;
   struct cgen_ctx ctx;
   unsigned i;

   ftype = tree_type(t);

   cgen_prototype(t, args, false);

   mangled = cgen_mangle_func_name(t);
   fn = LLVMGetNamedFunction(module, mangled);
   if (fn == NULL) {
      fn = LLVMAddFunction(module, mangled,
                           LLVMFunctionType(llvm_type(type_result(ftype)),
                                            args, type_params(ftype), false));
   }

   entry_bb = LLVMAppendBasicBlock(fn, "entry");
   LLVMPositionBuilderAtEnd(builder, entry_bb);

   ctx.entry_list = NULL;
   ctx.proc       = NULL;
   ctx.fdecl      = t;
   ctx.fn         = fn;

   for (i = 0; i < tree_ports(t); i++) {
      tree_t p = tree_port(t, i);
      switch (tree_class(p)) {
      case C_SIGNAL:
         tree_add_attr_ptr(p, sig_struct_i, LLVMGetParam(fn, i));
         break;

      case C_VARIABLE:
      case C_DEFAULT:
      case C_CONSTANT:
         tree_add_attr_ptr(p, local_var_i, LLVMGetParam(fn, i));
         break;

      case C_FILE:
         assert(false);
      }
   }

   tree_visit_only(t, cgen_func_vars, &ctx, T_VAR_DECL);

   for (i = 0; i < tree_stmts(t); i++)
      cgen_stmt(tree_stmt(t, i), &ctx);

   LLVMBuildUnreachable(builder);
}

static void cgen_proc_body(tree_t t)
{
   type_t ptype;
   LLVMTypeRef args[tree_ports(t)];
   const char *mangled;
   LLVMValueRef fn;
   LLVMBasicBlockRef entry_bb;
   struct cgen_ctx ctx;
   unsigned i;

   // Procedures take an extra "context" parameter which is used to support
   // suspending and resuming. If the procedure returns non-NULL then this
   // pointer should be saved, the caller should suspend, and we it resumes
   // call the procedure again with the saved pointer as the first argument.
   // If the procedure returns NULL execution continues as normal.
   // TODO: implement this

   ptype = tree_type(t);

   cgen_prototype(t, args, true);

   mangled = cgen_mangle_func_name(t);
   fn = LLVMGetNamedFunction(module, mangled);
   if (fn == NULL) {
      fn = LLVMAddFunction(module, mangled,
                           LLVMFunctionType(llvm_void_ptr(),
                                            args, type_params(ptype), false));
   }

   entry_bb = LLVMAppendBasicBlock(fn, "entry");
   LLVMPositionBuilderAtEnd(builder, entry_bb);

   ctx.entry_list = NULL;
   ctx.proc       = NULL;
   ctx.fdecl      = t;
   ctx.fn         = fn;

   for (i = 0; i < tree_ports(t); i++) {
      tree_t p = tree_port(t, i);
      switch (tree_class(p)) {
      case C_SIGNAL:
         tree_add_attr_ptr(p, sig_struct_i, LLVMGetParam(fn, i));
         break;

      case C_VARIABLE:
      case C_DEFAULT:
      case C_CONSTANT:
         tree_add_attr_ptr(p, local_var_i, LLVMGetParam(fn, i));
         break;

      case C_FILE:
         assert(false);
      }
   }

   // TODO: for procedures these should be placed in a dynamically
   //       allocated context struct
   tree_visit_only(t, cgen_func_vars, &ctx, T_VAR_DECL);

   for (i = 0; i < tree_stmts(t); i++)
      cgen_stmt(tree_stmt(t, i), &ctx);

   LLVMBuildRet(builder, LLVMConstNull(llvm_void_ptr()));
}

static void cgen_global_const(tree_t t)
{
   if (type_kind(tree_type(t)) == T_CARRAY) {
      tree_t value;
      LLVMValueRef c;

      value = tree_value(t);
      assert(tree_kind(value) == T_AGGREGATE);

      c = cgen_aggregate(value, NULL);
      tree_add_attr_ptr(t, local_var_i, c);
   }
}

static void cgen_top(tree_t t)
{
   unsigned i;
   for (i = 0; i < tree_decls(t); i++) {
      tree_t decl = tree_decl(t, i);
      switch (tree_kind(decl)) {
      case T_SIGNAL_DECL:
         cgen_signal(decl);
         break;
      case T_FUNC_BODY:
         cgen_func_body(decl);
         break;
      case T_ALIAS:
      case T_TYPE_DECL:
         break;
      case T_CONST_DECL:
         cgen_global_const(decl);
         break;
      case T_FUNC_DECL:
      case T_PROC_DECL:
         break;
      case T_PROC_BODY:
         cgen_proc_body(decl);
         break;
      default:
         assert(false);
      }
   }

   if (tree_kind(t) == T_ELAB) {
      for (i = 0; i < tree_stmts(t); i++)
         cgen_process(tree_stmt(t, i));
   }
}

static void optimise(void)
{
   LLVMPassManagerRef pass_mgr = LLVMCreatePassManager();

   LLVMAddPromoteMemoryToRegisterPass(pass_mgr);
   LLVMAddInstructionCombiningPass(pass_mgr);
   LLVMAddReassociatePass(pass_mgr);
   LLVMAddGVNPass(pass_mgr);
   LLVMAddCFGSimplificationPass(pass_mgr);

   LLVMRunPassManager(pass_mgr, module);
   LLVMDisposePassManager(pass_mgr);
}

static void cgen_support_fns(void)
{
   LLVMTypeRef _sched_process_args[] = { LLVMInt64Type() };
   LLVMTypeRef _sched_waveform_args[] = {
      llvm_void_ptr(),
      LLVMInt32Type(),
      LLVMInt64Type(),
      LLVMInt64Type()
   };
   LLVMTypeRef _sched_waveform_vec_args[] = {
      llvm_void_ptr(),
      LLVMInt32Type(),
      llvm_void_ptr(),
      LLVMInt32Type(),
      LLVMInt32Type(),
      LLVMInt64Type()
   };
   LLVMTypeRef _sched_event_args[] = {
      llvm_void_ptr(),
      LLVMInt32Type()
   };
   LLVMTypeRef _assert_fail_args[] = {
      LLVMPointerType(LLVMInt8Type(), 0),
      LLVMInt32Type(),
      LLVMInt8Type(),
      LLVMInt32Type(),
      LLVMPointerType(LLVMInt8Type(), 0)
   };
   LLVMTypeRef _array_copy_args[] = {
      llvm_void_ptr(),
      llvm_void_ptr(),
      LLVMInt32Type(),
      LLVMInt32Type(),
      LLVMInt32Type(),
      LLVMInt1Type()
   };
   LLVMTypeRef _image_args[] = {
      LLVMInt64Type(),
      LLVMInt32Type(),
      LLVMPointerType(LLVMInt8Type(), 0),
      LLVMPointerType(llvm_uarray_type(LLVMInt8Type()), 0)
   };
   LLVMTypeRef _tmp_alloc_args[] = {
      LLVMInt32Type(),
      LLVMInt32Type()
   };
   LLVMTypeRef _debug_out_args[] = {
      LLVMInt32Type()
   };
   LLVMTypeRef _iexp_args[] = {
      LLVMInt32Type(),
      LLVMInt32Type()
   };
   LLVMTypeRef _inst_name_args[] = {
      llvm_void_ptr(),
      LLVMPointerType(llvm_uarray_type(LLVMInt8Type()), 0)
   };

   LLVMAddFunction(module, "_sched_process",
                   LLVMFunctionType(LLVMVoidType(),
                                    _sched_process_args,
                                    ARRAY_LEN(_sched_process_args),
                                    false));
   LLVMAddFunction(module, "_sched_waveform",
                   LLVMFunctionType(LLVMVoidType(),
                                    _sched_waveform_args,
                                    ARRAY_LEN(_sched_waveform_args),
                                    false));
   LLVMAddFunction(module, "_sched_waveform_vec",
                   LLVMFunctionType(LLVMVoidType(),
                                    _sched_waveform_vec_args,
                                    ARRAY_LEN(_sched_waveform_vec_args),
                                    false));
   LLVMAddFunction(module, "_sched_event",
                   LLVMFunctionType(LLVMVoidType(),
                                    _sched_event_args,
                                    ARRAY_LEN(_sched_event_args),
                                    false));
   LLVMAddFunction(module, "_assert_fail",
                   LLVMFunctionType(LLVMVoidType(),
                                    _assert_fail_args,
                                    ARRAY_LEN(_assert_fail_args),
                                    false));
   LLVMAddFunction(module, "_array_copy",
                   LLVMFunctionType(LLVMVoidType(),
                                    _array_copy_args,
                                    ARRAY_LEN(_array_copy_args),
                                    false));
   LLVMAddFunction(module, "_image",
                   LLVMFunctionType(LLVMVoidType(),
                                    _image_args,
                                    ARRAY_LEN(_image_args),
                                    false));
   LLVMAddFunction(module, "_tmp_alloc",
                   LLVMFunctionType(llvm_void_ptr(),
                                    _tmp_alloc_args,
                                    ARRAY_LEN(_tmp_alloc_args),
                                    false));
   LLVMAddFunction(module, "_debug_out",
                   LLVMFunctionType(LLVMVoidType(),
                                    _debug_out_args,
                                    ARRAY_LEN(_debug_out_args),
                                    false));
   LLVMAddFunction(module, "_iexp",
                   LLVMFunctionType(LLVMInt32Type(),
                                    _iexp_args,
                                    ARRAY_LEN(_iexp_args),
                                    false));
   LLVMAddFunction(module, "_inst_name",
                   LLVMFunctionType(LLVMVoidType(),
                                    _inst_name_args,
                                    ARRAY_LEN(_inst_name_args),
                                    false));
}

static void cgen_module_name(tree_t top)
{
   const char *name_str = istr(tree_ident(top));

   size_t len = strlen(name_str);
   LLVMValueRef chars[len + 1];
   llvm_str(chars, len + 1, name_str);

   mod_name = LLVMAddGlobal(module,
                            LLVMArrayType(LLVMInt8Type(), len + 1),
                            "module_name");
   LLVMSetInitializer(mod_name,
                      LLVMConstArray(LLVMInt8Type(), chars, len + 1));
   LLVMSetLinkage(mod_name, LLVMPrivateLinkage);
}

void cgen(tree_t top)
{
   tree_kind_t kind;
   char fname[256];
   FILE *f;

   var_offset_i = ident_new("var_offset");
   local_var_i  = ident_new("local_var");
   sig_struct_i = ident_new("sig_struct");
   foreign_i    = ident_new("FOREIGN");

   kind = tree_kind(top);
   if (kind != T_ELAB && kind != T_PACK_BODY)
      fatal("cannot generate code for tree kind %d", kind);

   module = LLVMModuleCreateWithName(istr(tree_ident(top)));
   builder = LLVMCreateBuilder();

   cgen_module_name(top);
   cgen_support_fns();

   cgen_top(top);

   if (opt_get_int("dump-llvm"))
      LLVMDumpModule(module);

   if (LLVMVerifyModule(module, LLVMPrintMessageAction, NULL))
      fatal("LLVM verification failed");

   if (opt_get_int("optimise"))
      optimise();

   snprintf(fname, sizeof(fname), "_%s.bc", istr(tree_ident(top)));

   f = lib_fopen(lib_work(), fname, "w");
   if (LLVMWriteBitcodeToFD(module, fileno(f), 0, 0) != 0)
      fatal("error writing LLVM bitcode");
   fclose(f);

   LLVMDisposeBuilder(builder);
   LLVMDisposeModule(module);
}

