check_PROGRAMS = test_lib test_ident test_parse test_sem test_simp \
	test_elab test_heap
TESTS_ENVIRONMENT = BUILD_DIR=$(top_builddir)
TESTS = $(check_PROGRAMS) run_regr.rb

DEFAULT_INCLUDES = -iquote $(top_builddir) -iquote $(builddir) -iquote $(srcdir) -iquote $(top_builddir)/src -iquote $(top_srcdir)/src
AM_CFLAGS = -DTESTDIR=\"$(top_srcdir)/test\" \
	$(CHECK_CFLAGS)
LDADD = $(top_builddir)/src/rt/libnvc-rt.a $(top_builddir)/src/libnvc.a $(CHECK_LIBS) $(CURSES_LIB)
AM_LDFLAGS = -rdynamic

test_lib_SOURCES = test_lib.c
test_ident_SOURCES = test_ident.c
test_parse_SOURCES = test_parse.c
test_sem_SOURCES = test_sem.c
test_simp_SOURCES = test_simp.c

clean-local:
	-test -d logs && $(RM) -r logs
