noinst_LIBRARIES = libnvc-rt.a libjit.a

DEFAULT_INCLUDES = -iquote $(top_builddir) -iquote $(builddir) -iquote $(srcdir) -iquote $(top_builddir)/src -iquote $(top_srcdir)/src
AM_CFLAGS = -Wall -Werror

libnvc_rt_a_SOURCES = rtkern.c slave.c shell.c alloc.c vcd.c heap.c \
	pprint.c

libjit_a_SOURCES = jit.c
libjit_a_CFLAGS = $(AM_CFLAGS) $(LLVM_CFLAGS)
