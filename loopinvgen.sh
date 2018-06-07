#!/bin/bash

SELF_DIR="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"

BIN_DIR="$SELF_DIR/_bin"

RECORD="$BIN_DIR/lig-record"
INFER="$BIN_DIR/lig-infer"
VERIFY="$BIN_DIR/lig-verify"

if [ ! -f $RECORD ] || [ ! -f $INFER ] || [ ! -f $VERIFY ] ; then
  echo -en "
Building OCaml modules ...
" >&2 ; jbuilder build @localbin
fi

trap 'jobs -p | xargs kill -TERM > /dev/null 2> /dev/null' INT
trap "kill -KILL -`ps -o ppid= $$` > /dev/null 2> /dev/null" QUIT TERM

INTERMEDIATES_DIR="$SELF_DIR/_log"
SYGUS_EXT=".sl"
Z3_PATH="$SELF_DIR/_dep/z3"

INFER_TIMEOUT=60
MIN_INFER_TIMEOUT=5

RECORD_TIMEOUT=0.25s
RECORD_FORKS=4
RECORD_STATES_PER_FORK=256
MIN_RECORD_STATES_PER_FORK=63

RECORD_LOG=""
INFER_LOG=""
VERIFY_LOG=""

RECORD_ARGS=""
INFER_ARGS=""
VERIFY_ARGS=""

DO_LOG="no"
DO_CLEAN="no"
DO_VERIFY="no"

DO_INTERACTIVE="no"
show_status() {
  if [ "$DO_INTERACTIVE" == "yes" ] ; then
    echo -en "$1" >&2
    printf %16s%0"$(( ${#1} + 16 ))"d | tr 0 \\b >&2
  fi
}

usage() {
  if [ -n "$1" ] ; then echo -e "\nERROR: $1" >&2 ; fi
  echo -en "
Usage: $0 [options] <benchmark.sl>

Flags:
    [--clean-intermediates, -c]
    [--interactive, -i]
    [--verify, -v]

Configuration:
    [--intermediates-dir, -p <path>]  (_log)
    [--logging, -l <mode>]            (none)\t{none|rec|inf|all}
    [--record-states, -s <count>]     ($RECORD_STATES_PER_FORK)\t{> $MIN_RECORD_STATES_PER_FORK}
    [--infer-timeout, -t <seconds>]   ($INFER_TIMEOUT)\t{> $MIN_INFER_TIMEOUT}
    [--z3-path, -z <path>]            (_dep/z3)

Arguments to Internal Programs:
    [--Record-args, -R \"<args>\"]    for ${RECORD}
    [--Infer-args, -I \"<args>\"]     for ${INFER}
    [--Verify-args, -V \"<args>\"]    for ${VERIFY}
" >&2 ; exit -1
}

OPTS=`getopt -n 'parse-options' -o :R:I:V:icvl:p:s:t:z: --long Record-args:,Infer-args:,Verify-args:,interactive,clean-intermediates,verify,logging:,intermediates-dir:,record-states:,infer-timeout:,z3-path: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -R | --Record-args )
         RECORD_ARGS="$2"
         shift ; shift ;;
    -I | --Infer-args )
         INFER_ARGS="$2"
         shift ; shift ;;
    -V | --Verify-args )
         VERIFY_ARGS="$2"
         shift ; shift ;;

    -i | --interactive )
         DO_INTERACTIVE="yes" ; shift ;;
    -c | --clean-intermediates )
         DO_CLEAN="yes" ; shift ;;
    -v | --verify )
         DO_VERIFY="yes" ; shift ;;

    -l | --logging )
         [ "$2" == "none" ] || [ "$2" == "rec" ] || \
         [ "$2" == "inf" ] || [ "$2" == "all" ] || usage "Unknown source [$2] for logging."
         DO_LOG="$2"
         shift ; shift ;;
    -p | --intermediates-dir )
         INTERMEDIATES_DIR="$2"
         shift ; shift ;;
    -s | --record-states )
         [ "$2" -gt "$MIN_RECORD_STATES_PER_FORK" ] || usage "$2 must be > $MIN_RECORD_STATES_PER_FORK."
         STATES="$2"
         shift ; shift ;;
    -t | --infer-timeout )
         [ "$2" -gt "$MIN_INFER_TIMEOUT" ] || usage "$2 must be > $MIN_INFER_TIMEOUT."
         INFER_TIMEOUT="$2"
         shift ; shift ;;
    -z | --z3-path )
         [ -f "$2" ] || usage "Z3 [$2] not found."
         Z3_PATH="$2"
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

[ -d "$INTERMEDIATES_DIR" ] || mkdir -p "$INTERMEDIATES_DIR"
[ -d "$INTERMEDIATES_DIR" ] || usage "Intermediates directory [$INTERMEDIATES_DIR] not found."

TESTCASE="$1"
[ -f "$TESTCASE" ] || usage "Input file [$TESTCASE] not found."

TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
TESTCASE_PREFIX="$INTERMEDIATES_DIR/$TESTCASE_NAME"
TESTCASE_INVARIANT="$TESTCASE_PREFIX.inv"

TESTCASE_LOG="$TESTCASE_PREFIX.log"
TESTCASE_REC_LOG="$TESTCASE_PREFIX.rlog"
TESTCASE_REC_LOG_PATTERN="$TESTCASE_REC_LOG"?

TESTCASE_STATE="$TESTCASE_PREFIX.s"
TESTCASE_STATE_PATTERN="$TESTCASE_STATE"?
TESTCASE_ALL_STATES="$TESTCASE_PREFIX.states"

RECORD="$RECORD -z $Z3_PATH"
INFER="$INFER -z $Z3_PATH"
VERIFY="$VERIFY -z $Z3_PATH"

INFER_TIMEOUT="${INFER_TIMEOUT}s"

if [ "$DO_LOG" == "all" ] ; then
  RECORD_LOG="-l $TESTCASE_REC_LOG"
  INFER_LOG="-l $TESTCASE_LOG"
  VERIFY_LOG="-l $TESTCASE_LOG"
elif [ "$DO_LOG" == "rec" ] ; then
  RECORD_LOG="-l $TESTCASE_REC_LOG"
elif [ "$DO_LOG" == "inf" ] ; then
  INFER_LOG="-l $TESTCASE_LOG"
fi

rm -rf $TESTCASE_INVARIANT $TESTCASE_STATE_PATTERN $TESTCASE_ALL_STATES

if [ "$DO_LOG" != "none" ] ; then echo -en '' > "$TESTCASE_LOG" ; fi


show_status "(@ record)"

for i in `seq 1 $RECORD_FORKS` ; do
  if [ -n "$RECORD_LOG" ] ; then LOG_PARAM="$RECORD_LOG$i" ; else LOG_PARAM="" ; fi
  (timeout $RECORD_TIMEOUT \
           $RECORD -s $RECORD_STATES_PER_FORK -e "seed$i"  \
                   -o $TESTCASE_STATE$i $LOG_PARAM         \
                   $RECORD_ARGS $TESTCASE) >&2 &
done
wait

grep -hv "^[[:space:]]*$" $TESTCASE_STATE_PATTERN | sort -u > $TESTCASE_ALL_STATES

if [ -n "$RECORD_LOG" ] ; then cat $TESTCASE_REC_LOG_PATTERN > $TESTCASE_LOG ; fi


show_status "(@ infer)"

timeout --foreground $INFER_TIMEOUT \
        $INFER -s $TESTCASE_ALL_STATES -o $TESTCASE_INVARIANT $TESTCASE \
               $INFER_ARGS $INFER_LOG >&2
INFER_RESULT_CODE=$?


if [ "$DO_VERIFY" = "yes" ] ; then
  if [ $INFER_RESULT_CODE == 124 ] || [ $INFER_RESULT_CODE == 137 ] ; then
    echo > $TESTCASE_INVARIANT ; echo -n "[TIMEOUT] "
  fi

  show_status "(@ verify)"

  touch $TESTCASE_INVARIANT
  $VERIFY -i $TESTCASE_INVARIANT $VERIFY_LOG $VERIFY_ARGS $TESTCASE > "$TESTCASE_PREFIX.result"
  RESULT_CODE=$?

  show_status "" ; cat "$TESTCASE_PREFIX.result"
elif [ $INFER_RESULT_CODE == 0 ] ; then
  cat $TESTCASE_INVARIANT ; echo
  RESULT_CODE=0
fi


if [ "$DO_CLEAN" == "yes" ] ; then
  rm -rf $TESTCASE_STATE_PATTERN $TESTCASE_REC_LOG_PATTERN
  if [ $INFER_RESULT_CODE == 0 ] || [ $INFER_RESULT_CODE == 2 ] ; then
    rm -rf $TESTCASE_ALL_STATES
  fi
fi

exit $RESULT_CODE