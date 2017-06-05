#!/bin/bash

RESULT_FILE="_logs/RESULT"

echo > $RESULT_FILE
for b in benchmarks/*/*.sl ; do
  echo -n "$b => " | tee -a $RESULT_FILE
  (time ./verify.sh -cr -t 120 $b) 2>> $RESULT_FILE | tee -a $RESULT_FILE
  echo >> $RESULT_FILE
done

print_counts () {
  while (( "$#" )) ; do
    echo -n "$1 = " ; grep "$1" $RESULT_FILE | wc -l
    shift
  done
}

print_counts PASS FAIL TIMEOUT