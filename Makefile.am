SUBDIRS = src lib test

EXTRA_DIST = autogen.sh

ACLOCAL_AMFLAGS = -I m4
LIBTOOL_DEPS = @LIBTOOL_DEPS@

bootstrap: all
	@cd lib && $(MAKE) $(AM_MAKEFLAGS) bootstrap

libtool: $(LIBTOOL_DEPS)
	$(SHELL) ./config.status --recheck

.PHONY: bootstrap
