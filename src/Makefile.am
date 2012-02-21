SUBDIRS = rt

bin_PROGRAMS = nvc
noinst_LIBRARIES = libcgen.a libnvc.a

AM_CFLAGS = -Wall -Werror
AM_YFLAGS = -d --locations --report=all

BUILT_SOURCES = parse.h

libnvc_a_SOURCES = lib.c util.c ident.c parse.y lexer.l tree.c type.c \
	sem.c elab.c simp.c driver.c dump.c opt.c link.c

libcgen_a_SOURCES = cgen.c
libcgen_a_CFLAGS = $(AM_CFLAGS) $(LLVM_CFLAGS)

nvc_SOURCES = nvc.c

# Force C++ linking
nodist_EXTRA_nvc_SOURCES = dummy.cxx

if ON_WIN32
AM_LDFLAGS = @LDFLAGS@ -no-undefined -module -avoid-version -shared $(LLVM_LDFLAGS)
lib_LTLIBRARIES = libnvc-stub.la
libnvc_stub_la_SOURCES = lib.c util.c ident.c parse.y lexer.l tree.c type.c \
	sem.c elab.c simp.c driver.c dump.c opt.c link.c \
	cgen.c \
	rt/rtkern.c rt/slave.c rt/shell.c rt/alloc.c rt/vcd.c rt/heap.c \
	rt/jit.c
# See configure.ac for detail of @I_BARRIER@
# libtool adds -D_GNU_SOURCE, then ""_GNU_SOURCE" redefined" warning appears.
# libtool adds -DNDEBUG, then "control reaches end of non-void function" warning appears.
libnvc_stub_la_CFLAGS = $(AM_CFLAGS) -I$(srcdir)/rt @I_BARRIER@ $(LLVM_CFLAGS) -U_GNU_SOURCE -UNDEBUG
libnvc_stub_la_LIBADD = $(LLVM_LIBS) $(CURSES_LIB)
nvc_LDADD = libnvc-stub.la $(LLVM_LIBS) $(CURSES_LIB)
else
AM_LDFLAGS = -rdynamic $(LLVM_LDFLAGS)
nvc_LDADD = libnvc.a libcgen.a rt/libnvc-rt.a rt/libjit.a $(LLVM_LIBS) \
	$(CURSES_LIB)
endif
