noinst_LIBRARIES = libnvc-rt.a libjit.a

# See configure.ac for detail of @I_BARRIER@
AM_CFLAGS = -Wall -Werror -I$(srcdir)/.. @I_BARRIER@

libnvc_rt_a_SOURCES = rtkern.c slave.c shell.c alloc.c vcd.c heap.c

libjit_a_SOURCES = jit.c
libjit_a_CFLAGS = $(AM_CFLAGS) $(LLVM_CFLAGS)
