#!/bin/bash

LOG_PATH="_logs"
SYGUS_EXT=".sl"

BENCHMARK="$1"
BENCHMARK_NAME=`basename "$BENCHMARK" "$SYGUS_EXT"`
BENCHMARK_META="$LOG_PATH/$BENCHMARK_NAME.meta"
BENCHMARK_STATES="$LOG_PATH/$BENCHMARK_NAME.states"?
BENCHMARK_ALL_STATES="$LOG_PATH/$BENCHMARK_NAME.states"

# Record valid program states
./recorder.native -s 0 -m $BENCHMARK_META $BENCHMARK
for i in `seq 1 4` ; do
  ./recorder.native -r "just$i" -r "some$i" -r "random$i" -r "strings$i" \
                    -s 128 -o "$LOG_PATH/$BENCHMARK_NAME.states$i"       \
                    $BENCHMARK > /dev/null &
done

wait

tail -n 1 $BENCHMARK_META > $BENCHMARK_ALL_STATES
grep -hv "^[[:space:]]*$" $BENCHMARK_STATES | sort -u >> $BENCHMARK_ALL_STATES
rm -rf $BENCHMARK_STATES