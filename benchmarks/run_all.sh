#!/bin/bash

LOG_PATH="_log"
SYGUS_EXT=".sl"

TIMEOUT="$1"
(( TIMEOUT > 0 )) || TIMEOUT="60"

TIMEFORMAT=$'\nreal\t%3R\nuser\t%3U\n sys\t%3S\ncpu%%\t%P'

for TESTCASE in benchmarks/*/*.sl ; do
  TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
  TESTCASE_PREFIX="$LOG_PATH/$TESTCASE_NAME"
  TESTCASE_RESULT="$TESTCASE_PREFIX.result"

  echo -n "$TESTCASE => "

  if [ -f "$TESTCASE_RESULT" ] ; then
    OLD_VERDICT=`tail -n 6 $TESTCASE_RESULT | head -n 1`
    if [[ "$OLD_VERDICT" =~ ^PASS.* ]] ; then
      echo "SKIPPED (PASSING)"
      continue
    fi
  fi

  echo > $TESTCASE_RESULT
  (time ./loopinvgen.sh -cr -t "$TIMEOUT" $TESTCASE) \
    2>> $TESTCASE_RESULT | tee -a $TESTCASE_RESULT
done

print_counts () {
  while (( "$#" )) ; do
    echo -n "* $1 = "
    cat $LOG_PATH/*.result | grep "$1" | wc -l
    shift
  done
}

print_counts PASS FAIL TIMEOUT

PASSING_FILES=`grep -l "^PASS\$" $LOG_PATH/*.result`
PASSING_TIMES=`grep real $PASSING_FILES | cut -f2`
echo -e "\nPASS Stats:"
echo -e "time\n$PASSING_TIMES" | datamash -H min 1 max 1 mean 1 median 1 sum 1