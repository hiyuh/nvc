# NOTE: cygwin libtool is broken...
libtoolize --ltdl --copy --force && \
	cd libltdl && \
		echo "#undef __WINDOWS__" > acconfig.h && \
		autoheader && \
		sed -i \
			-e 's/AC_OUTPUT/case $host_os in cygwin* | mingw* | pw32*) AC_DEFINE(__WINDOWS__) ;; esac ; AC_OUTPUT/' \
			configure.ac && \
		autoconf && \
	cd ..
aclocal -I m4
autoconf
automake -a
