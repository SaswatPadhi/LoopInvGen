#!/bin/bash

SELF_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

trap 'jobs -p | xargs kill -INT > /dev/null 2> /dev/null' INT
trap "kill -9 -`ps -o pgid= $$` > /dev/null 2> /dev/null" QUIT TERM

SYGUS_EXT=".sl"
RESULT_EXT=".res"

LOG_PATH="$SELF_DIR/_log"
Z3_PATH="$SELF_DIR/_dep/z3"

TIMEOUT="60"
TOOL="$SELF_DIR/loopinvgen.sh"
VERIFY="$SELF_DIR/_bin/lig-verify"

show_status() {
  MSG="$1                " ; MSG_LEN=${#MSG}
  echo -en "$MSG" >&2
  printf %0"$MSG_LEN"d | tr 0 \\b >&2
}

usage() {
  echo -en "
Usage: $0 [options] -b <benchmarks_path> -- [tool specific options]

Configuration:
    --benchmarks, -b <path>
    [--log-path, -l <path>]           ($LOG_PATH)
    [--time-out, -m <seconds>]        ($TIMEOUT)
    [--tool, -t <path>]               ($TOOL)
    [--z3-path, -z <path>]            ($Z3_PATH)
" 1>&2 ; exit -1
}

OPTS=`getopt -n 'parse-options' -o :b:l:m:t:z: --long benchmarks:,log-path:,time-out:,tool:,z3-path: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -b | --benchmarks )
         BENCHMARKS_DIR="`realpath \"$2\"`"
         shift ; shift ;;
    -l | --log-path )
         LOG_PATH="$2"
         shift ; shift ;;
    -m | --time-out )
         TIMEOUT="$2"
         shift ; shift ;;
    -t | --tool )
         TOOL="$2"
         shift ; shift ;;
    -z | --z3-path )
         [ -f "$2" ] || usage
         Z3_PATH="$2"
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

VERIFY="$VERIFY -z $Z3_PATH"
TOOL_ARGS="$@"

# This is NOT dead code. Don't remove!
TIME=$'\nreal\t%e\nuser\t%U\n sys\t%S\ncpu%%\t%P'
TIMEFORMAT=$'\nreal\t%R\nuser\t%U\n sys\t%S\ncpu%%\t%P'

mkdir -p "$LOG_PATH"

COUNTER=0
for TESTCASE in `find "$BENCHMARKS_DIR" -name *$SYGUS_EXT` ; do
  TESTCASE_NAME=${TESTCASE#$BENCHMARKS_DIR}
  TESTCASE_NAME=${TESTCASE_NAME%$SYGUS_EXT}
  TESTCASE_PREFIX="$LOG_PATH/$TESTCASE_NAME.t_all"

  mkdir -p "`dirname \"$TESTCASE_PREFIX\"`"

  TESTCASE_RES="$TESTCASE_PREFIX$RESULT_EXT"
  TESTCASE_INV="$TESTCASE_PREFIX.inv"

  (( COUNTER++ ))
  printf "[%4d] $TESTCASE => " $COUNTER

  if [ -f "$TESTCASE_RES" ] ; then
    OLD_VERDICT=`tail -n 1 $TESTCASE_RES`
    if [[ "$OLD_VERDICT" =~ .*PASS.* ]] ; then
      TESTCASE_REAL_TIME=`grep "real" $TESTCASE_RES | cut -f2`
      echo "[SKIPPED] PASS @ $TESTCASE_REAL_TIME"
      continue
    fi
  fi

  show_status "(@ infer)"
  (time timeout --foreground --kill-after=$TIMEOUT $TIMEOUT \
                $TOOL $TESTCASE $TOOL_ARGS) > $TESTCASE_INV 2> $TESTCASE_RES
  INFER_RESULT_CODE=$?

  if [ $INFER_RESULT_CODE == 124 ] || [ $INFER_RESULT_CODE == 137 ] ; then
    echo -n "[TIMEOUT]" | tee -a $TESTCASE_RES
  fi

  show_status "(@ verify)"
  touch $TESTCASE_INV
  $VERIFY -i $TESTCASE_INV $TESTCASE | tee -a $TESTCASE_RES

  TESTCASE_REAL_TIME=`grep "real" $TESTCASE_RES | cut -f2`
  echo " @ $TESTCASE_REAL_TIME"
done

print_counts () {
  while (( "$#" )) ; do
    echo -n "* $1 = "
    cat `find $LOG_PATH -name *$RESULT_EXT` | grep "$1" | wc -l
    shift
  done
}

echo ""
print_counts PASS FAIL

echo ""
print_counts TIMEOUT

PASSING_TIMES="0"
RESULT_FILES="`find $LOG_PATH -name *$RESULT_EXT`"

if [ -n "$PASSING_FILES" ]; then
  PASSING_FILES="`grep -l PASS`"
  if [ -n "$PASSING_FILES" ]; then
    PASSING_TIMES=`grep real $PASSING_FILES | cut -f2`
  fi
fi

echo -e "\nPASS Stats:"
echo -e "time\n$PASSING_TIMES" | awk '{
  if(NR == 1) {
    header = $1
    next
  }

  data[i++] = $1
  sum += $1;

  if(min == "") min = max = $1;

  if($1 > max) max = $1;
  else if($1 < min) min = $1;
}
END {
  printf "MIN(%s) = %0.3f\n", header, min
  printf "MED(%s) = %0.3f\n", header, data[int((i-1)/2)]
  printf "AVG(%s) = %0.3f\n", header, sum/i
  printf "MAX(%s) = %0.3f\n", header, max
  printf "SUM(%s) = %0.3f\n", header, sum
}'