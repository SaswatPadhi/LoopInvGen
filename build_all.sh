#!/bin/bash

usage() {
  echo "
Usage: $0 [flags]

Flags:
    [--debug, -D]             Create a debug build (minimal optimization and allows logging)
    [--star-exec, -S]         Generate package for running on StarExec
    [--with-logging, -L]      Enable logging within the LoopInvGen binaries

Configuration:
    [--jobs, -j <num>]        Use <num> jobs for building LoopInvGen (and z3)
    [--build-z3, -z <path>]   Also create a statically-linked build of z3
" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :DSLj:z: --long debug,star-exec,with-logging,jobs:,build-z3: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

JOBS="`cat /proc/cpuinfo | grep processor | wc -l`"

WITH_LOGGING=""
MAKE_Z3_AT=""
MAKE_STAREXEC=""
MAKE_DEBUG=""

STAREXEC_ARCHIVE_NAME="LoopInvGen_SyGuS_INV.tgz"

while true ; do
  case "$1" in
    -D | --debug )
         MAKE_DEBUG="YES"
         shift ;;
    -S | --star-exec )
         MAKE_STAREXEC="YES" ;
         shift ;;
    -L | --with-logging )
         WITH_LOGGING="YES" ;
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

if [ -n "$MAKE_Z3_AT" ] ; then
  LIG_DIR=`pwd`
  Z3_BUILD_DIR="build_for_pie"
  cd "$MAKE_Z3_AT"

  rm -rf "$Z3_BUILD_DIR"
  mkdir -p "$Z3_BUILD_DIR"

  python2.7 scripts/mk_make.py --staticbin --staticlib \
                               --build "$Z3_BUILD_DIR"

  cd "$Z3_BUILD_DIR"
  make -j "$JOBS"

  mkdir -p "$LIG_DIR/_dep"
  cp z3 "$LIG_DIR/_dep/z3"
  cd "$LIG_DIR"
fi

if [ -n "$WITH_LOGGING" ] ; then
  dune build @Logging || exit $?
else
  dune build @NoLog || exit $?
fi

if [ -n "$MAKE_DEBUG" ] ; then
  dune build --profile debug -j "$JOBS" || exit $?
else
  dune build --profile optimize -j "$JOBS" || exit $?
fi

if [ -z "$MAKE_STAREXEC" ] ; then exit 0 ; fi

rm -rf starexec && mkdir -p starexec/bin/_bin

cp -rL _dep starexec/bin
cp -L _build/install/default/bin/* starexec/bin/_bin
rm -rf starexec/bin/_bin/lig-verify

STAREXEC_DEFAULT_CONFIG_FILE="starexec/bin/starexec_run_default"
STAREXEC_DEBUG_CONFIG_FILE="starexec/bin/starexec_run_IGNORE-debug"

cat > "$STAREXEC_DEFAULT_CONFIG_FILE" << "EOF"
#!/bin/bash

trap 'jobs -p | xargs kill -INT > /dev/null 2> /dev/null' INT
trap "kill -KILL -`ps -o ppid= $$` > /dev/null 2> /dev/null" QUIT TERM

TESTCASE="$1"
TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"

RECORD_FORKS=4
RECORD_TIMEOUT=0.33s
RECORD_STATES_PER_FORK=256

_bin/lig-process -o $TESTCASE_NAME.pro $TESTCASE >&2 || exit 1

for i in `seq 1 $RECORD_FORKS` ; do
  (timeout --kill-after=$RECORD_TIMEOUT $RECORD_TIMEOUT                      \
           _bin/lig-record -z _dep/z3 -s $RECORD_STATES_PER_FORK -e "seed$i" \
                           -o $TESTCASE_NAME.r$i $TESTCASE_NAME.pro) >&2 &
done
wait

grep -hv "^[[:space:]]*$" $TESTCASE_NAME.r* | sort -u > $TESTCASE_NAME.states

_bin/lig-infer -z _dep/z3 -s $TESTCASE_NAME.states $TESTCASE_NAME.pro
EOF
chmod +x "$STAREXEC_DEFAULT_CONFIG_FILE"

cat > "$STAREXEC_DEBUG_CONFIG_FILE" << "EOF"
#!/bin/bash

pwd
ls -lah

file _dep/z3 _bin/lig-process _bin/lig-record _bin/lig-infer
ldd _dep/z3 _bin/lig-process _bin/lig-record _bin/lig-infer

_dep/z3
_bin/lig-process -h
_bin/lig-record -h
_bin/lig-infer -h
EOF
chmod +x "$STAREXEC_DEBUG_CONFIG_FILE"

cat <<EOF > starexec/starexec_description.txt
A loop invariant inference tool built using PIE: precondition inference engine.

https://github.com/SaswatPadhi/LoopInvGen
EOF

chmod -R 777 starexec/bin

echo -e "\nPreparing starexec package (starexec/):"
cd starexec
tar cvzf "../$STAREXEC_ARCHIVE_NAME" ./*
echo -e "\nPackage saved to $STAREXEC_ARCHIVE_NAME"