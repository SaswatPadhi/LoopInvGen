#!/bin/bash

usage() {
  echo "
Usage: $0 [flags]

Flags:
    [--debug, -D]             Create a debug build (little optimization + logging support)
    [--star-exec, -S]         Generate package for running on StarExec

Configuration:
    [--build-z3, -z <path>]   Also create a statically-linked build of z3
    [--jobs, -j <num>]        Use <num> jobs for building LoopInvGen (and z3)
" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :DSj:z: --long debug,starexec,jobs:,build-z3: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

JOBS="`cat /proc/cpuinfo | grep processor | wc -l`"

MAKE_Z3_AT=""
MAKE_STAREXEC=""
MAKE_DEBUG=""

while true ; do
  case "$1" in
    -D | --debug )
         MAKE_DEBUG="YES"
         shift ;;
    -S | --star-exec )
         MAKE_STAREXEC="YES" ;
         shift ;;
    -j | --jobs )
         JOBS="$2" ;
         shift ; shift ;;
    -z | --build-z3 )
         MAKE_Z3_AT="$2" ;
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

if [ -n "$MAKE_DEBUG" ] ; then
  jbuilder build @debug
else
  jbuilder build @optimize
fi

if [ -n "$MAKE_Z3_AT" ] ; then
  LIG=`pwd`
  Z3_BUILD_DIR="build_for_pie"
  cd "$MAKE_Z3_AT"

  rm -rf "$Z3_BUILD_DIR"
  mkdir -p "$Z3_BUILD_DIR"

  python2.7 scripts/mk_make.py --staticbin --staticlib \
                               --build "$Z3_BUILD_DIR"

  cd "$Z3_BUILD_DIR"
  make -j "$JOBS"

  mkdir -p "$LIG/_dep"
  cp z3 "$LIG/_dep/z3"
  cd "$LIG"
fi

jbuilder build @local -j "$JOBS"
if [ -z "$MAKE_STAREXEC" ] ; then exit 0 ; fi

rm -rf starexec && mkdir -p starexec/bin

cp -rL _bin _dep starexec/bin
rm -rf starexec/bin/_bin/lig-verify

cat << "EOF" > starexec/bin/starexec_run_default
#!/bin/bash

TESTCASE="$1"
TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"

RECORD_FORKS=3
RECORD_TIMEOUT=0.3s
RECORD_STATES_PER_FORK=512

for i in `seq 1 $RECORD_FORKS` ; do
  (timeout --kill-after=$RECORD_TIMEOUT $RECORD_TIMEOUT           \
           _bin/lig-record -z _dep/z3 -s $RECORD_STATES_PER_FORK  \
                           -r "seed$i" -o $TESTCASE_NAME.r$i $TESTCASE) >&2 &
done
wait

grep -hv "^[[:space:]]*$" $TESTCASE_NAME.r* | sort -u > $TESTCASE_NAME.states

_bin/lig-infer -z _dep/z3 -s $TESTCASE_NAME.states $TESTCASE
EOF
chmod +x starexec/bin/starexec_run_default

cat << "EOF" > starexec/bin/starexec_run_debug
#!/bin/bash

pwd
ls -lah

file _dep/z3 _bin/lig-record _bin/lig-infer
ldd _dep/z3 _bin/lig-record _bin/lig-infer

_dep/z3
_bin/lig-record -h
_bin/lig-infer -h
EOF
chmod +x starexec/bin/starexec_run_debug

cat <<EOF > starexec/starexec_description.txt
A loop invariant inference tool built using PIE: precondition inference engine.

https://github.com/SaswatPadhi/LoopInvGen
EOF

chmod -R 777 starexec/bin

echo -ne "\nPreparing starexec package (starexec/):\n"
cd starexec
tar cvzf ../LoopInvGen_SyGuS_INV.tgz ./*