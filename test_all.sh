#!/bin/bash

LOG_PATH="_log"
SYGUS_EXT=".sl"

TOOL="./loopinvgen.sh"

usage() {
  echo -en "
Usage: $0 [-t <tool> -l <log_path>] -b <benchmarks_path> -- [tool_specific_options]

Configuration:
    --benchmarks, -b <path>
    [--log-path, -l <path>]           ($LOG_PATH}
    [--tool, -t <path>]               ($TOOL)
" 1>&2 ; exit -1
}

OPTS=`getopt -n 'parse-options' -o :b:l:t: --long benchmarks:,log-path,tool: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -b | --benchmarks )
         BENCHMARKS="$2"
         shift ; shift ;;
    -l | --log-path )
         LOG_PATH="$2"
         shift ; shift ;;
    -t | --tool )
         TOOL="$2"
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

TOOL_ARGS="$1"

# This is NOT dead code. Don't remove!
TIMEFORMAT=$'\nreal\t%3R\nuser\t%3U\n sys\t%3S\ncpu%%\t%P'

mkdir -p $LOG_PATH

COUNTER=0
for TESTCASE in `find "$BENCHMARKS" -iname *$SYGUS_EXT` ; do
  TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
  TESTCASE_PREFIX="$LOG_PATH/$TESTCASE_NAME"
  TESTCASE_RES="$TESTCASE_PREFIX.result"

  (( COUNTER++ ))
  printf "[%4d] $TESTCASE => " $COUNTER

  if [ -f "$TESTCASE_RES" ] ; then
    OLD_VERDICT=`tail -n 5 $TESTCASE_RES | head -n 1`
    if [[ "$OLD_VERDICT" =~ .*PASS.* ]] ; then
      TESTCASE_REAL_TIME=`grep "real" $TESTCASE_RES | cut -f2`
      echo "[SKIPPED] PASS @ $TESTCASE_REAL_TIME"
      continue
    fi
  fi

  echo > $TESTCASE_RES
  (time $TOOL $TESTCASE $TOOL_ARGS) 2>> $TESTCASE_RES | tee -a $TESTCASE_RES

  TESTCASE_REAL_TIME=`grep "real" $TESTCASE_RES | cut -f2`
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