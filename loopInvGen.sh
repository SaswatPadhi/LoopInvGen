#!/bin/bash

LOG_PATH="_logs"
SYGUS_EXT=".sl"

BENCHMARK="$1"
BENCHMARK_NAME="`basename "$BENCHMARK" "$SYGUS_EXT"`"
BENCHMARK_META="$LOG_PATH/$BENCHMARK_NAME.meta"
BENCHMARK_STATE="$LOG_PATH/$BENCHMARK_NAME.s"
BENCHMARK_STATE_PATTERN="$BENCHMARK_STATE"?
BENCHMARK_ALL_STATES="$BENCHMARK_STATE""tate"

STEPS=1024

for i in `seq 1 4` ; do
  ./recorder.native -s $STEPS -r "seed$i"    \
                    -o $BENCHMARK_STATE$i   \
                     $BENCHMARK > /dev/null &
done

./recorder.native -s $STEPS -r "seed"    \
                  -m $BENCHMARK_META     \
                  -o $BENCHMARK_STATE"0" \
                  $BENCHMARK > /dev/null

wait

tail -n 1 $BENCHMARK_META > $BENCHMARK_ALL_STATES
grep -hv "^[[:space:]]*$" $BENCHMARK_STATE_PATTERN | sort -u >> $BENCHMARK_ALL_STATES
rm -rf $BENCHMARK_STATE_PATTERN