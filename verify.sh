#!/bin/bash

LOG_PATH="_logs"
SYGUS_EXT=".sl"

CHECK="./Check.native"
RECORD="./Record.native"
INFER="./Infer.native"

FORKS=2
STEPS=512

TIMEOUT=360s

CHECK_LOG=""
RECORD_LOG=""
INFER_LOG=""

DO_CHECK="no"
DO_REMOVE_LOGS="no"

usage() {
  echo "Usage: $0 [-c] [-l] [-r] [-s {$STEPS} <count>] [-t {360} <seconds>] testcase" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :clm:rs:t: --long check,logging,max-states:,remove-logs,simulation-steps:,timeout: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -c | --check )
         DO_CHECK="yes" ; shift ;;
    -l | --logging )
         VERIFIER_LOG="-l" ; shift ;;
    -r | --remove-logs )
         DO_REMOVE_LOGS="yes" ; shift ;;
    -s | --simulation-steps )
         STEPS=$2
         (( STEPS > 0 )) || usage
         shift ; shift ;;
    -t | --timeout )
         TIMEOUT=$2
         (( TIMEOUT > 0 )) || usage
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

TESTCASE_STATE="$TESTCASE_PREFIX.s"
TESTCASE_STATE_PATTERN="$TESTCASE_STATE"?
TESTCASE_ALL_STATES="$TESTCASE_PREFIX.states"

TESTCASE_ROOT="$TESTCASE_PREFIX.r"
TESTCASE_ROOT_PATTERN="$TESTCASE_ROOT"?
TESTCASE_ALL_ROOTS="$TESTCASE_PREFIX.roots"

for i in `seq 1 $FORKS` ; do
  $RECORD -s $STEPS -r "seed$i" -o $TESTCASE_STATE$i $TESTCASE \
          -h $TESTCASE_ROOT$i $RECORD_LOG >&2 &
done

$RECORD -s $STEPS -r "seed0" -o $TESTCASE_STATE"0" $TESTCASE \
        -h $TESTCASE_ROOT"0" $RECORD_LOG >&2

wait

grep -hv "^[[:space:]]*$" $TESTCASE_ROOT_PATTERN | sort -u > $TESTCASE_ALL_ROOTS
grep -hv "^[[:space:]]*$" $TESTCASE_STATE_PATTERN | sort -u > $TESTCASE_ALL_STATES

if [ $DO_REMOVE_LOGS = "yes" ]; then
  rm -rf $TESTCASE_ROOT_PATTERN
  rm -rf $TESTCASE_STATE_PATTERN
fi

timeout --kill-after=$TIMEOUT $TIMEOUT \
        $INFER -s $TESTCASE_ALL_STATES -o $TESTCASE_INVARIANT $TESTCASE \
               -h $TESTCASE_ALL_ROOTS $INFER_LOG >&2
RESULT_CODE=$?

if [ $RESULT_CODE == 0 ] && [ $DO_REMOVE_LOGS = "yes" ] ; then
  rm -rf $TESTCASE_ALL_ROOTS $TESTCASE_ALL_STATES
fi

if [ $DO_CHECK = "yes" ]; then
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