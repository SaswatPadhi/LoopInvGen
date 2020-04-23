#!/usr/bin/env bash

set -Eeuo pipefail

if (( ${BASH_VERSION%%.*} < 4 )); then echo "ERROR: [bash] version 4.0+ required!" ; exit -1 ; fi

ROOT="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)/.."

usage() {
  if [ -n "$1" ]; then echo -e "\nERROR: $1" >&2 ; fi
  echo -en "
Usage: $0 [flags]

Flags:
    [--debug, -D]             Create a debug build (minimal optimization and allows logging)
    [--starexec, -S]         Generate package for running on StarExec
    [--with-logging, -L]      Enable logging within the LoopInvGen binaries

Configuration:
    [--jobs, -j <num>]        Use <num> jobs for building LoopInvGen (and z3)
    [--build-z3, -z <path>]   Also create a statically-linked build of z3
" 1>&2 ; exit 1
}

JOBS="`getconf _NPROCESSORS_ONLN`"

WITH_LOGGING=""
MAKE_Z3_AT=""
MAKE_STAREXEC=""
MAKE_DEBUG=""

STAREXEC_ARCHIVE_NAME="LoopInvGen_SyGuS_INV.tgz"

for opt in "$@"; do
  shift
  case "$opt" in
    "--debug")        set -- "$@" "-D" ;;
    "--starexec")     set -- "$@" "-S" ;;
    "--with-logging") set -- "$@" "-L" ;;
    "--jobs")         set -- "$@" "-j" ;;
    "--build-z3")     set -- "$@" "-z" ;;

    "--")             set -- "$@" "--" ;;
    "--"*)            usage "Unrecognized option: $opt." ;;
    *)                set -- "$@" "$opt"
  esac
done

OPTIND=1
while getopts ':DSLj:z:' OPTION ; do
  case "$OPTION" in
    "D" ) MAKE_DEBUG="YES" ;;
    "S" ) MAKE_STAREXEC="YES" ;;
    "L" ) WITH_LOGGING="YES" ;;
    "j" ) JOBS="$OPTARG" ;;
    "z" ) MAKE_Z3_AT="`realpath "$OPTARG"`" ;;
      * ) usage "Unrecognized option: -$OPTARG." ;;
  esac
done
shift $(($OPTIND -1))

if [ -n "$MAKE_Z3_AT" ] ; then
  Z3_BUILD_DIR="build_for_lig"
  cd "$MAKE_Z3_AT"

  rm -rf "$Z3_BUILD_DIR"
  mkdir -p "$Z3_BUILD_DIR"

  if [ -n "$MAKE_STAREXEC" ] ; then
    python3 scripts/mk_make.py --staticbin --staticlib \
                               --build "$Z3_BUILD_DIR"
  else
    python3 scripts/mk_make.py --build "$Z3_BUILD_DIR"
  fi

  cd "$Z3_BUILD_DIR"
  make -j "$JOBS"

  mkdir -p "$ROOT/_dep"
  cp z3 "$ROOT/_dep/z3"
fi

cd "$ROOT"

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

rm -rf _starexec && mkdir -p _starexec/bin/_bin

cp -rL _dep _starexec/bin
cp -L _build/install/default/bin/* _starexec/bin/_bin
rm -rf _starexec/bin/_bin/lig-verify \
       _starexec/bin/_bin/lig-score  \
       _starexec/bin/_bin/lig-tools-*

STAREXEC_GPLEARN_CONFIG_FILE="_starexec/bin/starexec_run_gplearn"
STAREXEC_DEFAULT_CONFIG_FILE="_starexec/bin/starexec_run_default"

cat > "$STAREXEC_DEFAULT_CONFIG_FILE" << "EOF"
#!/usr/bin/env bash

set -m
trap 'kill -KILL -$PID_1 -$PID_2 -$PID_3 &> /dev/null' QUIT TERM

TESTCASE="$1"
TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"

RECORD_TIMEOUT=0.35s
RECORD_STATES_PER_FORK=256

_bin/lig-process -z _dep/z3 -o "$TESTCASE_NAME.pro" "$TESTCASE" > "$TESTCASE_NAME.inv"
[ $? == 0 ] || exit 1

if [ -s "$TESTCASE_NAME.inv" ]; then
  cat "$TESTCASE_NAME.inv" ; exit 0
fi

trigger() {
  if [ -s "$TESTCASE_NAME.inv_a" ] || [ -s "$TESTCASE_NAME.inv_b" ] || [ -s "$TESTCASE_NAME.inv_c" ]; then
    trap - SIGCHLD ; trap '' SIGCHLD
  else
    return
  fi

  if [ -s "$TESTCASE_NAME.inv_a" ]; then
    cat "$TESTCASE_NAME.inv_a"
  elif [ -s "$TESTCASE_NAME.inv_b" ]; then
    cat "$TESTCASE_NAME.inv_b"
  elif [ -s "$TESTCASE_NAME.inv_c" ]; then
    cat "$TESTCASE_NAME.inv_c"
  fi

  kill -KILL -$PID_1 -$PID_2 -$PID_3 &> /dev/null
  exit 0
}

for i in `seq 1 3` ; do
  (timeout --kill-after=$RECORD_TIMEOUT $RECORD_TIMEOUT                                            \
           _bin/lig-record -z _dep/z3 -s $RECORD_STATES_PER_FORK -r "seed$i" "$TESTCASE_NAME.pro") \
           > "$TESTCASE_NAME.r$i" &
done

timeout --kill-after=$RECORD_TIMEOUT $RECORD_TIMEOUT                                               \
        _bin/lig-record -z _dep/z3 -s $RECORD_STATES_PER_FORK -r "seed4" "$TESTCASE_NAME.pro"      \
        > "$TESTCASE_NAME.r4"
wait

grep -hv "^[[:space:]]*$" "$TESTCASE_NAME.r"* | sort -u > "$TESTCASE_NAME.states"

trap trigger SIGCHLD 2> /dev/null

_bin/lig-infer -max-conflict-group-size 32 -num-counterexamples 32 -z _dep/z3                      \
               -s "$TESTCASE_NAME.states" "$TESTCASE_NAME.pro" > $TESTCASE_NAME.inv_a &
PID_1=$!

_bin/lig-infer -max-conflict-group-size 128 -num-counterexamples 32 -z _dep/z3                     \
               -s "$TESTCASE_NAME.states" "$TESTCASE_NAME.pro" > $TESTCASE_NAME.inv_a &
PID_2=$!

(timeout --kill-after=$RECORD_TIMEOUT $RECORD_TIMEOUT                                              \
         _bin/lig-record -z _dep/z3 -s $RECORD_STATES_PER_FORK -r "seed5" "$TESTCASE_NAME.pro")    \
         > "$TESTCASE_NAME.r5" &
PID_REC=$!
timeout --kill-after=$RECORD_TIMEOUT $RECORD_TIMEOUT                                               \
        _bin/lig-record -z _dep/z3 -s $RECORD_STATES_PER_FORK -r "seed6" "$TESTCASE_NAME.pro"      \
        > "$TESTCASE_NAME.r6"
wait $PID_REC

grep -hv "^[[:space:]]*$" "$TESTCASE_NAME.r"* | sort -u > "$TESTCASE_NAME.states"

_bin/lig-infer -max-conflict-group-size 64 -num-counterexamples 32 -z _dep/z3                      \
               -s "$TESTCASE_NAME.states" "$TESTCASE_NAME.pro" > $TESTCASE_NAME.inv_c &
PID_3=$!

wait 2> /dev/null ; trigger
EOF
chmod +x "$STAREXEC_DEFAULT_CONFIG_FILE"

cat > "$STAREXEC_GPLEARN_CONFIG_FILE" << "EOF"
#!/usr/bin/env bash

set -m
trap 'kill -KILL -$PID_1 -$PID_2 -$PID_3 &> /dev/null' QUIT TERM

TESTCASE="$1"
TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"

RECORD_TIMEOUT=0.5s
RECORD_STATES_PER_FORK=512

_bin/lig-process -z _dep/z3 -o "$TESTCASE_NAME.pro" "$TESTCASE" > "$TESTCASE_NAME.inv"
[ $? == 0 ] || exit 1

if [ -s "$TESTCASE_NAME.inv" ]; then
  cat "$TESTCASE_NAME.inv" ; exit 0
fi

trigger() {
  if [ -s "$TESTCASE_NAME.inv_a" ] || [ -s "$TESTCASE_NAME.inv_b" ] || [ -s "$TESTCASE_NAME.inv_c" ]; then
    trap - SIGCHLD ; trap '' SIGCHLD
  else
    return
  fi

  if [ -s "$TESTCASE_NAME.inv_a" ]; then
    cat "$TESTCASE_NAME.inv_a"
  elif [ -s "$TESTCASE_NAME.inv_b" ]; then
    cat "$TESTCASE_NAME.inv_b"
  elif [ -s "$TESTCASE_NAME.inv_c" ]; then
    cat "$TESTCASE_NAME.inv_c"
  fi

  kill -KILL -$PID_1 -$PID_2 -$PID_3 &> /dev/null
  exit 0
}

for i in `seq 1 3` ; do
  (timeout --kill-after=$RECORD_TIMEOUT $RECORD_TIMEOUT                                            \
           _bin/lig-record -z _dep/z3 -s $RECORD_STATES_PER_FORK -r "seed$i" "$TESTCASE_NAME.pro") \
           > "$TESTCASE_NAME.r$i" &
done

timeout --kill-after=$RECORD_TIMEOUT $RECORD_TIMEOUT                                               \
        _bin/lig-record -z _dep/z3 -s $RECORD_STATES_PER_FORK -r "seed4" "$TESTCASE_NAME.pro"      \
        > "$TESTCASE_NAME.r4"
wait

grep -hv "^[[:space:]]*$" "$TESTCASE_NAME.r"* | sort -u > "$TESTCASE_NAME.states"

trap trigger SIGCHLD 2> /dev/null

_bin/lig-infer -max-conflict-group-size 32 -num-counterexamples 32 -max-expressiveness-level 2     \
               -z _dep/z3 -s "$TESTCASE_NAME.states" "$TESTCASE_NAME.pro" > $TESTCASE_NAME.inv_a &
PID_1=$!

_bin/lig-infer -max-conflict-group-size 128 -num-counterexamples 32 -max-expressiveness-level 3    \
               -z _dep/z3 -s "$TESTCASE_NAME.states" "$TESTCASE_NAME.pro" > $TESTCASE_NAME.inv_b &
PID_2=$!

_bin/lig-infer -max-conflict-group-size 64 -num-counterexamples 32 -max-expressiveness-level 4     \
               -z _dep/z3 -s "$TESTCASE_NAME.states" "$TESTCASE_NAME.pro" > $TESTCASE_NAME.inv_c &
PID_3=$!

wait 2> /dev/null ; trigger
EOF
chmod +x "$STAREXEC_GPLEARN_CONFIG_FILE"

cat <<EOF > _starexec/starexec_description.txt
A loop invariant inference tool built using PIE: precondition inference engine.

https://github.com/SaswatPadhi/LoopInvGen
EOF

chmod -R 777 _starexec/bin

echo -e "\nPreparing package for StarExec (from _starexec/):"
cd _starexec
tar cvzf "../$STAREXEC_ARCHIVE_NAME" *
echo -e "\nPackage saved to $STAREXEC_ARCHIVE_NAME"
