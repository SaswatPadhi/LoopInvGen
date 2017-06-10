#!/bin/bash

LOG_PATH="_logs"
SYGUS_EXT=".sl"
MIN_STEPS=128
MIN_TIMEOUT=6s
REC_TIMEOUT=3s

CHECK="./Check.native"
RECORD="./Record.native"
INFER="./Infer.native"

FORKS=2
STEPS=2048

TIMEOUT=360s

CHECK_LOG=""
RECORD_LOG=""
INFER_LOG=""

DO_LOG="no"
DO_CHECK="no"
DO_CLEAN="no"

usage() {
  echo "Usage: $0 [-c] [-l <rec|inf|all>] [-r] [-s <count> {> $MIN_STEPS} (default=$STEPS)] [-t <seconds> {> $MIN_TIMEOUT} (default=$TIMEOUT)] <.sl file>" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :cl:m:rs:t: --long check,logging:,max-states:,remove-logs,simulation-steps:,timeout: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -c | --check )
         DO_CHECK="yes" ; shift ;;
    -l | --logging )
         [ "$2" == "rec" ] || [ "$2" == "inf" ] || [ "$2" == "all" ] || usage
         DO_LOG="$2"
         shift ; shift ;;
    -r | --remove-logs )
         DO_CLEAN="yes" ; shift ;;
    -s | --simulation-steps )
         STEPS=$2
         (( STEPS > 128 )) || usage
         shift ; shift ;;
    -t | --timeout )
         TIMEOUT=$2
         (( TIMEOUT > 6 )) || usage
         TIMEOUT="$2s"
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

TESTCASE="$1"

TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
TESTCASE_PREFIX="$LOG_PATH/$TESTCASE_NAME"
TESTCASE_INVARIANT="$TESTCASE_PREFIX.inv"

TESTCASE_REC_LOG="$TESTCASE_PREFIX.rlog"
TESTCASE_REC_LOG_PATTERN="$TESTCASE_REC_LOG"?
TESTCASE_LOG="$TESTCASE_PREFIX.log"

TESTCASE_STATE="$TESTCASE_PREFIX.s"
TESTCASE_STATE_PATTERN="$TESTCASE_STATE"?
TESTCASE_ALL_STATES="$TESTCASE_PREFIX.states"

TESTCASE_ROOT="$TESTCASE_PREFIX.r"
TESTCASE_ROOT_PATTERN="$TESTCASE_ROOT"?
TESTCASE_ALL_ROOTS="$TESTCASE_PREFIX.roots"

if [ "$DO_LOG" == "all" ] ; then
  RECORD_LOG="-l $TESTCASE_REC_LOG"
  INFER_LOG="-l $TESTCASE_LOG"
elif [ "$DO_LOG" == "rec" ] ; then
  RECORD_LOG="-l $TESTCASE_REC_LOG"
elif [ "$DO_LOG" == "inf" ] ; then
  INFER_LOG="-l $TESTCASE_LOG"
fi

for i in `seq 1 $FORKS` ; do
  if [ -n "$RECORD_LOG" ] ; then LOG_PARAM="$RECORD_LOG$i" ; else LOG_PARAM="" ; fi
  (timeout --kill-after=$REC_TIMEOUT $REC_TIMEOUT \
           $RECORD -s $STEPS -r "seed$i" -o $TESTCASE_STATE$i $TESTCASE \
                   -h $TESTCASE_ROOT$i $LOG_PARAM) >&2 &
done

if [ -n "$RECORD_LOG" ] ; then LOG_PARAM="$RECORD_LOG"0 ; else LOG_PARAM="" ; fi
(timeout --kill-after=$REC_TIMEOUT $REC_TIMEOUT \
         $RECORD -s $STEPS -r "seed0" -o $TESTCASE_STATE"0" $TESTCASE \
                 -h $TESTCASE_ROOT"0" $LOG_PARAM) >&2

wait

grep -hv "^[[:space:]]*$" $TESTCASE_ROOT_PATTERN | sort -u > $TESTCASE_ALL_ROOTS
grep -hv "^[[:space:]]*$" $TESTCASE_STATE_PATTERN | sort -u > $TESTCASE_ALL_STATES

if [ -n "$RECORD_LOG" ] ; then
  cat $TESTCASE_REC_LOG_PATTERN > $TESTCASE_LOG
fi

if [ "$DO_CLEAN" == "yes" ]; then
  rm -rf $TESTCASE_ROOT_PATTERN
  rm -rf $TESTCASE_STATE_PATTERN
  rm -rf $TESTCASE_REC_LOG_PATTERN
fi

timeout --kill-after=$TIMEOUT $TIMEOUT \
        $INFER -s $TESTCASE_ALL_STATES -o $TESTCASE_INVARIANT $TESTCASE \
               -h $TESTCASE_ALL_ROOTS $INFER_LOG >&2
RESULT_CODE=$?

if [ $RESULT_CODE == 0 ] && [ "$DO_CLEAN" == "yes" ] ; then
  rm -rf $TESTCASE_ALL_ROOTS $TESTCASE_ALL_STATES
fi

if [ "$DO_CHECK" = "yes" ]; then
  if [ $RESULT_CODE == 124 ] || [ $RESULT_CODE == 137 ] ; then
    echo "TIMEOUT" ; exit $RESULT_CODE
  fi

  $CHECK -i $TESTCASE_INVARIANT $CHECK_LOG $TESTCASE
  exit $?
else
  if [ $RESULT_CODE == 0 ] ; then
    cat $TESTCASE_INVARIANT ; echo ; exit 0
  fi
fi