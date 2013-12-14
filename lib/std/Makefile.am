stddir = $(pkgdatadir)/std
std_DATA = std/_NVC_LIB std/STD.STANDARD std/STD.TEXTIO std/_STD.TEXTIO.bc \
	std/STD.TEXTIO-body std/_STD.TEXTIO-body.bc

std/STD.TEXTIO-body: std/STD.TEXTIO
std/_STD.TEXTIO.bc: std/STD.TEXTIO
std/_STD.TEXTIO-body.bc: std/STD.TEXTIO

if ENABLE_NATIVE
std_so = std/_STD.TEXTIO.so std/_STD.TEXTIO-body.so

std/_STD.TEXTIO.so: std/STD.TEXTIO
std/_STD.TEXTIO-body.so: std/STD.TEXTIO

if IMPLIB_REQUIRED
std_DATA += std/_STD.TEXTIO.a std/_STD.TEXTIO-body.a

std/_STD.TEXTIO.a: std/STD.TEXTIO
std/_STD.TEXTIO-body.a: std/STD.TEXTIO

# Using SCRIPTS rather than data ensures execute bit gets set on Cygwin
std_SCRIPTS = $(std_so)
else

std_DATA += $(std_so)

endif

endif

bootstrap: $(std_DATA)

std/_NVC_LIB: std/STD.STANDARD

std/STD.STANDARD: $(srcdir)/standard.vhd
	$(nvc) --work=std -a --bootstrap $(srcdir)/standard.vhd

std/STD.TEXTIO: $(srcdir)/textio.vhd std/STD.STANDARD
	$(nvc) --work=std -a $(srcdir)/textio.vhd
	$(codegen) --work=std --codegen textio

clean-local:
	-test -d std && $(RM) -r std

include ../nvc.mk
