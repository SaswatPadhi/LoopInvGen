#!/bin/bash

LOG_PATH="_logs"
SYGUS_EXT=".sl"

CHECKER="./Checker.native"
RECORDER="./Recorder.native"
VERIFIER="./Verifier.native"

STEPS=768
MAX_STATES=2048

TIMEOUT=300s

CHECKER_LOG=""
RECORDER_LOG=""
VERIFIER_LOG=""

CHECK="no"
REMOVE_LOGS="no"

usage() {
  echo "Usage: $0 -c -l -r [-s {$STEPS} <count>] [-t {300} <seconds>] testcase" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :clrs:t: --long check,logging,remove-logs,simulation-steps:,timeout: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -c | --check )
         CHECK="yes" ; shift ;;
    -l | --logging )
         CHECKER_LOG=""
         RECORDER_LOG=""
         VERIFIER_LOG="-l"
         shift ;;
    -r | --remove-logs )
         REMOVE_LOGS="yes" ; shift ;;
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
TESTCASE_STATE="$TESTCASE_PREFIX.s"
TESTCASE_STATE_PATTERN="$TESTCASE_STATE"?
TESTCASE_ALL_STATES="$TESTCASE_PREFIX.states"
TESTCASE_INVARIANT="$TESTCASE_PREFIX.inv"

for i in `seq 1 4` ; do
  $RECORDER -s $STEPS -r "seed$i" -o $TESTCASE_STATE$i $TESTCASE \
            $RECORDER_LOG >&2 &
done

$RECORDER -s $STEPS -r "seed0" -o $TESTCASE_STATE"0" $TESTCASE \
          $RECORDER_LOG >&2

wait

grep -hv "^[[:space:]]*$" $TESTCASE_STATE_PATTERN \
  | sort -u | shuf | head -n $MAX_STATES \
  > $TESTCASE_ALL_STATES

if [ $REMOVE_LOGS = "yes" ]; then
  rm -rf $TESTCASE_STATE_PATTERN
fi

timeout --kill-after=$TIMEOUT $TIMEOUT \
        $VERIFIER -s $TESTCASE_ALL_STATES -o $TESTCASE_INVARIANT $TESTCASE \
                  $VERIFIER_LOG >&2
RESULT_CODE=$?
if [ $RESULT_CODE == 0 ] && [ $REMOVE_LOGS = "yes" ] ; then
  rm -rf $TESTCASE_ALL_STATES
fi

if [ $CHECK = "yes" ]; then
  if [ $RESULT_CODE == 0 ] ; then
    $CHECKER -i $TESTCASE_INVARIANT $CHECKER_LOG $TESTCASE
  elif [ $RESULT_CODE == 124 ] || [ $RESULT_CODE == 137 ] ; then
    echo "TIMEOUT"
  else
    echo "FAIL"
  fi
else
  if [ $RESULT_CODE == 0 ] ; then
    cat $TESTCASE_INVARIANT ; echo
  fi
fi