#!/bin/bash

INTERMEDIATES_DIR="_log"
SYGUS_EXT=".sl"
Z3_PATH="_dep/z3.bin"

MIN_STEPS=63
MIN_TIMEOUT=5
REC_TIMEOUT=3s

RECORD="./Record.native"
INFER="./Infer.native"
VERIFY="./Verify.native"

FORKS=1
STEPS=512

TIMEOUT=360

RECORD_LOG=""
INFER_LOG=""
VERIFY_LOG=""

DO_LOG="no"
DO_CLEAN="no"
DO_VERIFY="no"

usage() {
  echo "
Usage: $0 [flags] <benchmark.sl>

Flags:
    [--verify, -v]
    [--intermediates-path, -i <path>] (_log)
    [--logging, -l <mode>] (none) {none|rec|inf|all}
    [--remove-intermediates, -r]
    [--steps-to-simulate, -s <count>] ($STEPS) {> $MIN_STEPS}
    [--timeout, -t <seconds>] ($TIMEOUT) {> $MIN_TIMEOUT}
    [--z3-path, -z <path>] (_dep/z3.bin)
" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :vi:l:rs:t:z: --long verify,intermediate-path:,logging:,remove-intermediates,steps-to-simulate:,timeout:,z3-path: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -v | --verify )
         DO_VERIFY="yes" ; shift ;;
    -i | --intermediates-path )
         [ -d "$2" ] || usage
         INTERMEDIATES_DIR="$2"
         shift ; shift ;;
    -l | --logging )
         [ "$2" == "none" ] || [ "$2" == "rec" ] || \
         [ "$2" == "inf" ] || [ "$2" == "all" ] || usage
         DO_LOG="$2"
         shift ; shift ;;
    -r | --remove-intermediates )
         DO_CLEAN="yes" ; shift ;;
    -s | --steps-to-simulate )
         [ "$2" -gt "$MIN_STEPS" ] || usage
         STEPS="$2"
         shift ; shift ;;
    -t | --timeout )
         [ "$2" -gt "$MIN_TIMEOUT" ] || usage
         TIMEOUT="$2"
         shift ; shift ;;
    -z | --z3-path )
         [ -f "$2" ] || usage
         Z3_PATH="$2"
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

RECORD="$RECORD -z $Z3_PATH"
INFER="$INFER -z $Z3_PATH"
VERIFY="$VERIFY -z $Z3_PATH"
TIMEOUT="${TIMEOUT}s"

TESTCASE="$1"

TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
TESTCASE_PREFIX="$INTERMEDIATES_DIR/$TESTCASE_NAME"
TESTCASE_INVARIANT="$TESTCASE_PREFIX.inv"

TESTCASE_REC_LOG="$TESTCASE_PREFIX.rlog"
TESTCASE_REC_LOG_PATTERN="$TESTCASE_REC_LOG"?
TESTCASE_LOG="$TESTCASE_PREFIX.log"

TESTCASE_STATE="$TESTCASE_PREFIX.s"
TESTCASE_STATE_PATTERN="$TESTCASE_STATE"?
TESTCASE_ALL_STATES="$TESTCASE_PREFIX.states"

if [ "$DO_LOG" == "all" ] ; then
  RECORD_LOG="-l $TESTCASE_REC_LOG"
  INFER_LOG="-l $TESTCASE_LOG"
  VERIFY_LOG="-l $TESTCASE_LOG"
elif [ "$DO_LOG" == "rec" ] ; then
  RECORD_LOG="-l $TESTCASE_REC_LOG"
elif [ "$DO_LOG" == "inf" ] ; then
  INFER_LOG="-l $TESTCASE_LOG"
fi

for i in `seq 1 $FORKS` ; do
  if [ -n "$RECORD_LOG" ] ; then LOG_PARAM="$RECORD_LOG$i" ; else LOG_PARAM="" ; fi
  (timeout --kill-after=$REC_TIMEOUT $REC_TIMEOUT \
           $RECORD -s $STEPS -r "seed$i" -o $TESTCASE_STATE$i $LOG_PARAM \
                   $TESTCASE) >&2 &
done

if [ -n "$RECORD_LOG" ] ; then LOG_PARAM="$RECORD_LOG"0 ; else LOG_PARAM="" ; fi
(timeout --kill-after=$REC_TIMEOUT $REC_TIMEOUT \
         $RECORD -s $STEPS -r "seed0" -o $TESTCASE_STATE"0" $LOG_PARAM \
                 $TESTCASE) >&2

wait

grep -hv "^[[:space:]]*$" $TESTCASE_STATE_PATTERN | sort -u > $TESTCASE_ALL_STATES
if [ -n "$RECORD_LOG" ] ; then cat $TESTCASE_REC_LOG_PATTERN > $TESTCASE_LOG ; fi

if [ "$DO_CLEAN" == "yes" ]; then
  rm -rf $TESTCASE_STATE_PATTERN $TESTCASE_REC_LOG_PATTERN
fi

timeout --kill-after=$TIMEOUT $TIMEOUT \
        $INFER -s $TESTCASE_ALL_STATES -o $TESTCASE_INVARIANT $TESTCASE \
               $INFER_LOG >&2
RESULT_CODE=$?

if ( [ $RESULT_CODE == 0 ] || [ $RESULT_CODE == 2 ] ) && [ "$DO_CLEAN" == "yes" ] ; then
  rm -rf $TESTCASE_ALL_STATES
fi

if [ "$DO_VERIFY" = "yes" ]; then
  if [ $RESULT_CODE == 124 ] || [ $RESULT_CODE == 137 ] ; then
    echo > $TESTCASE_INVARIANT ; echo -n "[TIMEOUT] "
  fi

  $VERIFY -i $TESTCASE_INVARIANT $VERIFY_LOG $TESTCASE
  exit $?
elif [ $RESULT_CODE == 0 ] ; then
  cat $TESTCASE_INVARIANT ; echo
fi
exit $RESULT_CODE
