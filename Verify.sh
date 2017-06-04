#!/bin/bash

LOG_PATH="_logs"
SYGUS_EXT=".sl"

RECORDER="./Recorder.native"
VERIFIER="./Verifier.native"

STEPS=1536
TIMEOUT=5m
RECORDER_LOG=""
VERIFIER_LOG=""

usage() {
  echo "Usage: $0 [-l {none} <none|verifier|all>] [-s {$STEPS} <uint>] [-t {5m} <duration>] benchmark" 1>&2 ;
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
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

BENCHMARK="$1"

BENCHMARK_NAME="`basename "$BENCHMARK" "$SYGUS_EXT"`"
BENCHMARK_PREFIX="$LOG_PATH/$BENCHMARK_NAME"
BENCHMARK_STATE="$BENCHMARK_PREFIX.s"
BENCHMARK_STATE_PATTERN="$BENCHMARK_STATE"?
BENCHMARK_ALL_STATES="$BENCHMARK_PREFIX.states"
BENCHMARK_INVARIANT="$BENCHMARK_PREFIX.inv"

for i in `seq 1 4` ; do
  $RECORDER -s $STEPS -r "seed$i" -o $BENCHMARK_STATE$i $BENCHMARK \
            $RECORDER_LOG > /dev/null &
done

$RECORDER -s $STEPS -r "seed0" -o $BENCHMARK_STATE"0" $BENCHMARK \
          $RECORDER_LOG > /dev/null

wait

grep -hv "^[[:space:]]*$" $BENCHMARK_STATE_PATTERN \
  | sort -u > $BENCHMARK_ALL_STATES
rm -rf $BENCHMARK_STATE_PATTERN

timeout --kill-after=$TIMEOUT $TIMEOUT \
        $VERIFIER -s $BENCHMARK_ALL_STATES -o $BENCHMARK_INVARIANT $BENCHMARK \
                  $VERIFIER_LOG > /dev/null
if [ $? == 0 ] ; then rm -rf $BENCHMARK_ALL_STATES ; fi
