AC_INIT([nvc], [0.1],
        [Nick Gasson <nick@nick.me.uk>],
        [nvc])
AM_INIT_AUTOMAKE([color-tests])

AC_CONFIG_MACRO_DIR([m4])

AC_CANONICAL_HOST

AC_PROG_CC
AC_PROG_CC_C99
AM_PROG_CC_C_O
AC_PROG_CXX
AC_PROG_INSTALL
AC_PROG_MKDIR_P
AC_PROG_YACC
AM_PROG_LEX

# On cygwin, the dlsym function can only find symbols in a loaded DLL.
# If the symbol is in the .EXE file then the symbol doesn't get found.
# See also:
#  http://lists.cs.uiuc.edu/pipermail/llvmdev/2005-June/004364.html
LT_INIT([shared,static,win32-dll])
AC_SUBST([LIBTOOL_DEPS])

AC_C_INLINE

AC_TYPE_SIZE_T
AC_TYPE_SSIZE_T
AC_TYPE_INT8_T
AC_TYPE_INT16_T
AC_TYPE_INT32_T
AC_TYPE_INT64_T
AC_TYPE_UINT8_T
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T
AC_TYPE_UINT64_T
AC_TYPE_PID_T

AC_FUNC_MMAP
AC_FUNC_ALLOCA
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_FUNC_FORK
AC_CHECK_FUNCS([strdup mkdir realpath rmdir strerror strcasecmp \
                memset strchr strrchr strstr setenv])

AC_HEADER_STDBOOL
AC_CHECK_HEADERS([limits.h stddef.h fcntl.h libintl.h malloc.h \
                  sys/socket.h])

AC_CHECK_HEADERS([tcl.h tcl/tcl.h], [have_tcl=yes; break], [])
AC_SEARCH_LIBS([Tcl_CreateInterp], [tcl], [],
  [AC_ERROR(TCL library not found)])

if test ! "$have_tcl" = "yes"; then
  AC_ERROR(TCL header file not found)
fi

VL_LIB_READLINE
if test "$vl_cv_lib_readline" = "no"; then
  AC_WARN(terminal line editing will not be supported)
fi

AX_LLVM_C([engine bitreader bitwriter])

AX_WITH_CURSES

PKG_CHECK_MODULES([CHECK], [check >= 0.9.4], [], [])

AX_DEFINE_DIR([DATADIR], [datadir/nvc], [Installation data directory])

case $host_os in
  *cygwin* | *mingw* | *pw32*)
    ON_WIN32=yes

    # On cygwin, local headers can sometimes be included instead
    # of system ones which is worked around using -I-. A better
    # solution would be to have automake use -iquote.
    # And more bad news, libltdl does't build w/ -I-.
    # FIXME: mingw and pw32 really want it too?
    I_BARRIER=-I-
  ;;
esac
AC_SUBST(ON_WIN32)
AM_CONDITIONAL(ON_WIN32, test x"$ON_WIN32" = x"yes")
AC_SUBST(I_BARRIER)

AC_CONFIG_HEADERS([config.h])
AC_OUTPUT([Makefile src/Makefile src/rt/Makefile test/Makefile \
           lib/Makefile lib/std/Makefile lib/ieee/Makefile])
