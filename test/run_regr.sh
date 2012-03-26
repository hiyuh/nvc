#!/bin/dash

# FIXME: This script creates test/work, but "make check" expects no "test/work".
#        Before "make check", make sure no "test/work" yourself.
# FIXME: Implement logging functionalities like test/run_regr.rb?

# NOTE: cecho() does echo colorized all arguments, except 1st and 2nd.
#       Color is specified by 1st and 2nd argument for foreground and
#       background.
#       This colorize is made by VT100 display attributes.
cecho() {
	local attr="\033[" ;
	case $1 in
		black)   attr="${attr}30;" ; ;;
		red)     attr="${attr}31;" ; ;;
		green)   attr="${attr}32;" ; ;;
		yellow)  attr="${attr}33;" ; ;;
		blue)    attr="${attr}34;" ; ;;
		magenta) attr="${attr}35;" ; ;;
		cyan)    attr="${attr}36;" ; ;;
		white)   attr="${attr}37;" ; ;;
	esac ;
	case $2 in
		black)   attr="${attr}40m" ; ;;
		red)     attr="${attr}41m" ; ;;
		green)   attr="${attr}42m" ; ;;
		yellow)  attr="${attr}43m" ; ;;
		blue)    attr="${attr}44m" ; ;;
		magenta) attr="${attr}45m" ; ;;
		cyan)    attr="${attr}46m" ; ;;
		white)   attr="${attr}47m" ; ;;
	esac ;
	shift 2 ;
	echo "${attr}${*}\033[0m" ;
}

NVC="NVC_LIBPATH=../lib/std:../lib/ieee ../src/nvc" ;

# NOTE: eeval() does echo all arguments and evaluate them.
eeval() {
	cecho cyan black "$*" ;
	eval $* ;
}

# NOTE: analyze() does analyze VHDL file given by 1st argument using NVC
#       with EXTRA_AFLAGS.
analyze() {
	eeval ${NVC} -a ${EXTRA_AFLAGS} $1 ;
}

# NOTE: elaborate() does elaborate VHDL unit given by 1st argument using
#       NVC with EXTRA_EFLAGS.
elaborate() {
	eeval ${NVC} -e ${EXTRA_EFLAGS} $1 ;
}

# NOTE: run() does run VHDL unit given by 1st argument using NVC with
#       EXTRA_RFLAGS.
#       --stop-time option is generated from the given unit name, if required.
# FIXME: Generate --stop-time from regress/testlist.txt.
# FIXME: IMHO, regression should not have requirement to specify --stop-time,
#        except testing --stop-time functionality itself.
# FIXME: Implement expectation collation w/ regress/gold, if required.
run() {
	local RFLAGS ;
	case $1 in
		counter) RFLAGS="--stop-time=50ns"  ; ;;
		lfsr)    RFLAGS="--stop-time=510ns" ; ;;
		ieee2)   RFLAGS="--stop-time=15ns"  ; ;;
		*)       RFLAGS=""                  ; ;;
	esac ;
	eeval ${NVC} -r ${RFLAGS} ${EXTRA_RFLAGS} $1 ;
}

case $1 in
	analyze)
		shift 1 ;
		cecho yellow black "> analyze" ;
		case $1 in
			all)
				for v in regress/*.vhd ;
				do
					cecho yellow black ">> analyze ${v}" ;
					analyze ${v} ;
				done ;
			;;
			*)
				while [ $# -gt 0 ] ;
				do
					v="regress/${1}.vhd" ;
					cecho yellow black ">> analyze ${v}" ;
					analyze ${v} ;
					shift 1 ;
				done ;
			;;
		esac ;
	;;
	elaborate)
		shift 1 ;
		cecho yellow black "> elaborate" ;
		case $1 in
			all)
				for v in regress/*.vhd ;
				do
					u="$(basename ${v} | sed -e 's|.vhd||')" ;
					cecho yellow black ">> elaborate ${u}" ;
					elaborate ${u} ;
				done ;
			;;
			*)
				while [ $# -gt 0 ] ;
				do
					cecho yellow black ">> elaborate $1" ;
					elaborate $1 ;
					shift 1 ;
				done ;
			;;
		esac ;
	;;
	run)
		shift 1 ;
		cecho yellow black "> run" ;
		case $1 in
			all)
				for v in regress/*.vhd ;
				do
					u="$(basename ${v} | sed -e 's|.vhd||')" ;
					cecho yellow black ">> run ${u}" ;
					run ${u} ;
				done ;
			;;
			*)
				while [ $# -gt 0 ] ;
				do
					cecho yellow black ">> run $1" ;
					run $1 ;
					shift 1 ;
				done ;
			;;
		esac ;
	;;
	all)
		p="${0}" ;
		shift 1 ;
		${p} analyze   $* ;
		${p} elaborate $* ;
		${p} run       $* ;
	;;
	each)
		p="${0}" ;
		shift 1 ;
		case $1 in
			all)
				for v in regress/*.vhd ;
				do
					u="$(basename ${v} | sed -e 's|.vhd||')" ;
					${p} all ${u} ;
				done ;
			;;
			*)
				while [ $# -gt 0 ] ;
				do
					${p} all $1 ;
					shift 1 ;
				done ;
			;;
		esac ;
	;;
	*)
		cecho yellow black "ERROR: no target is specified." ;
		cecho yellow black "Usage: $(basename $0) [ analyze | elaborate | run | all | each ] [ all | unit ... ]" ;
	;;
esac ;
