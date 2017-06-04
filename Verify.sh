#!/bin/bash

LOG_PATH="_logs"
SYGUS_EXT=".sl"

CHECKER="./Checker.native"
RECORDER="./Recorder.native"
VERIFIER="./Verifier.native"

STEPS=1536
TIMEOUT=300s
RECORDER_LOG=""
VERIFIER_LOG=""

usage() {
  echo "Usage: $0 [-l {none} <none|verifier|all>] [-s {$STEPS} <count>] [-t {300} <seconds>] testcase" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :l:s:t: --long logging:,simulation-steps:,timeout: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -l | --logging )
         l="$2"
         if [ $l = "none" ] ; then
           RECORDER_LOG=""
           VERIFIER_LOG=""
         elif [ $l = "all" ] ; then
           RECORDER_LOG="-l"
           VERIFIER_LOG="-l"
         elif [ $l = "verifier" ] ; then
           RECORDER_LOG=""
           VERIFIER_LOG="-l"
         else
           usage
         fi
         shift ; shift ;;
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
  | sort -u > $TESTCASE_ALL_STATES
rm -rf $TESTCASE_STATE_PATTERN

timeout --kill-after=$TIMEOUT $TIMEOUT \
        $VERIFIER -s $TESTCASE_ALL_STATES -o $TESTCASE_INVARIANT $TESTCASE \
                  $VERIFIER_LOG >&2

if [ $? == 0 ] ; then
  rm -rf $TESTCASE_ALL_STATES
  $CHECKER -i $TESTCASE_INVARIANT $TESTCASE_LOG $TESTCASE
elif [ $? == 124 || $? == 137 ] ; then
  echo "TIMEOUT"
else
  echo "FAIL"
fi