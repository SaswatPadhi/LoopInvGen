#!/bin/bash

LOG_PATH="_log"
SYGUS_EXT=".sl"

TIMEOUT="60"
LOOPINVGEN_ARGS="$@"

# This is NOT dead code. Don't remove!
TIMEFORMAT=$'\nreal\t%3R\nuser\t%3U\n sys\t%3S\ncpu%%\t%P'

mkdir -p _log

COUNTER=0
for TESTCASE in benchmarks/*/*.sl ; do
  TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
  TESTCASE_PREFIX="$LOG_PATH/$TESTCASE_NAME"
  TESTCASE_RESULT="$TESTCASE_PREFIX.result"

  (( COUNTER++ ))
  printf "[%4d] $TESTCASE => " $COUNTER

  if [ -f "$TESTCASE_RESULT" ] ; then
    OLD_VERDICT=`tail -n 5 $TESTCASE_RESULT | head -n 1`
    if [[ "$OLD_VERDICT" =~ .*PASS.* ]] ; then
      TESTCASE_REAL_TIME=`grep "real" $TESTCASE_RESULT | cut -f2`
      echo "[SKIPPED] PASS @ $TESTCASE_REAL_TIME"
      continue
    fi
  fi

  echo > $TESTCASE_RESULT
  (time ./loopinvgen.sh -v -t "$TIMEOUT" $TESTCASE $LOOPINVGEN_ARGS) \
    2>> $TESTCASE_RESULT | tee -a $TESTCASE_RESULT

  TESTCASE_REAL_TIME=`grep "real" $TESTCASE_RESULT | cut -f2`
  echo " @ $TESTCASE_REAL_TIME"
done

print_counts () {
  while (( "$#" )) ; do
    echo -n "* $1 = "
    cat $LOG_PATH/*.result | grep "$1" | wc -l
    shift
  done
}

echo ""
print_counts PASS FAIL

echo ""
print_counts TIMEOUT

PASSING_FILES=`grep -l "PASS" $LOG_PATH/*.result`
PASSING_TIMES=`grep real $PASSING_FILES | cut -f2`

echo -e "\nPASS Stats:"
echo -e "time\n$PASSING_TIMES" | awk -f print_stats.awk