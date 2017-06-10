#!/bin/bash

LOG_PATH="_logs"
SYGUS_EXT=".sl"

TIMEOUT="$1"
(( TIMEOUT > 0 )) || TIMEOUT="64"

for TESTCASE in benchmarks/*/*.sl ; do
  TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
  TESTCASE_PREFIX="$LOG_PATH/$TESTCASE_NAME"
  TESTCASE_RESULT="$TESTCASE_PREFIX.result"

  echo -n "$TESTCASE => "

  if [ -f "$TESTCASE_RESULT" ] ; then
    OLD_VERDICT=`tail -n 5 $TESTCASE_RESULT | head -n 1`
    if [[ "$OLD_VERDICT" =~ ^PASS.* ]] ; then
      echo "SKIPPED (PASSING)"
      continue
    fi
  fi

  echo > $TESTCASE_RESULT
  (time ./verify.sh -cr -t "$TIMEOUT" $TESTCASE) 2>> $TESTCASE_RESULT | tee -a $TESTCASE_RESULT
done

print_counts () {
  while (( "$#" )) ; do
    cat $LOG_PATH/*.result | grep "$1" | wc -l
    shift
  done
}

print_counts PASS FAIL TIMEOUT