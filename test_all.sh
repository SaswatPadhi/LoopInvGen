#!/bin/bash

SELF_DIR="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"

trap 'kill -TERM -$INFER_PID > /dev/null 2> /dev/null' INT
trap "kill -KILL -`ps -o pgid= $$` > /dev/null 2> /dev/null" QUIT TERM

SYGUS_EXT=".sl"
RESULT_EXT=".res"
RERUN_CACHED=""

BENCHMARKS_DIR=""
LOGS_DIR="$SELF_DIR/_log"
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
  if [ -n "$1" ] ; then echo -e "\nERROR: $1" >&2 ; fi
  echo -en "
Usage: $0 [options] -b <benchmarks_path> -- [tool specific options]

Flags:
    [--rerun-cached, -r]

Configuration:
    --benchmarks, -b <path>
    [--logs-dir, -l <path>]           ($LOGS_DIR)
    [--time-out, -m <seconds>]        ($TIMEOUT)
    [--tool, -t <path>]               ($TOOL)
    [--z3-path, -z <path>]            ($Z3_PATH)
" 1>&2 ; exit -1
}

OPTS=`getopt -n 'parse-options' -o :b:l:m:rt:z: --long benchmarks:,logs-dir:,time-out:,rerun-cached,tool:,z3-path: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -b | --benchmarks )
         [ -d "$2" ] || usage "Benchmarks directory [$2] not found."
         BENCHMARKS_DIR="`realpath "$2"`"
         shift ; shift ;;
    -l | --logs-dir )
         LOGS_DIR="`realpath "$2"`"
         shift ; shift ;;
    -m | --time-out )
         TIMEOUT="$2"
         shift ; shift ;;
    -r | --rerun-cached )
         RERUN_CACHED="YES"
         shift ;;
    -t | --tool )
         [ -f "$2" ] || usage "Tool [$2] not found."
         TOOL="$2"
         shift ; shift ;;
    -z | --z3-path )
         [ -f "$2" ] || usage "Z3 [$2] not found."
         Z3_PATH="$2"
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

[ -d "$BENCHMARKS_DIR" ] || usage "Benchmarks directory [$BENCHMARKS_DIR] not found."

[ -d "$LOGS_DIR" ] || mkdir -p "$LOGS_DIR"
[ -d "$LOGS_DIR" ] || usage "Logs directory [$LOGS_DIR] not found."

VERIFY="$VERIFY -z $Z3_PATH"
TOOL_ARGS="$@"
TIMEOUT="${TIMEOUT}s"

# This is NOT dead code. Don't remove!
# Sets the output format for `time`
TIME=$'\nreal\t%e\nuser\t%U\n sys\t%S\ncpu%%\t%P'
TIMEFORMAT=$'\nreal\t%R\nuser\t%U\n sys\t%S\ncpu%%\t%P'

mkdir -p "$LOGS_DIR"

cd "`dirname "$TOOL"`"
TOOL="./`basename "$TOOL"`"

CSV_SUMMARY="$LOGS_DIR/summary.csv"
TXT_SUMMARY="$LOGS_DIR/summary.txt"

echo -n "" > "$TXT_SUMMARY"
echo "Benchmark,Verdict,Time" > "$CSV_SUMMARY"

COUNTER=0
for TESTCASE in `find "$BENCHMARKS_DIR" -name *$SYGUS_EXT` ; do
  TESTCASE_NAME=${TESTCASE#$BENCHMARKS_DIR/}
  TESTCASE_NAME=${TESTCASE_NAME%$SYGUS_EXT}
  TESTCASE_PREFIX="$LOGS_DIR/$TESTCASE_NAME.t_all"

  mkdir -p "`dirname \"$TESTCASE_PREFIX\"`"

  TESTCASE_RES="$TESTCASE_PREFIX$RESULT_EXT"
  TESTCASE_INV="$TESTCASE_PREFIX.inv"

  (( COUNTER++ ))
  printf "[%4d] %64s => " $COUNTER $TESTCASE_NAME

  if [ -z "$RERUN_CACHED" ] && [ -f "$TESTCASE_RES" ] ; then
    OLD_VERDICT=`tail -n 1 $TESTCASE_RES`
    if [[ "$OLD_VERDICT" =~ .*PASS.* ]] ; then
      TESTCASE_REAL_TIME=`grep "real" $TESTCASE_RES | cut -f2`
      printf "%07.3fs  @  [SKIPPED] $OLD_VERDICT\n" $TESTCASE_REAL_TIME
      echo "$TESTCASE,$OLD_VERDICT,$TESTCASE_REAL_TIME" >> "$CSV_SUMMARY"
      continue
    fi
  fi

  echo > $TESTCASE_INV ; echo > $TESTCASE_RES

  show_status "(@ infer)"
  (time timeout $TIMEOUT $TOOL $TESTCASE $TOOL_ARGS) > $TESTCASE_INV 2> $TESTCASE_RES &
  INFER_PID=$!
  wait $INFER_PID
  INFER_RESULT_CODE=$?

  TESTCASE_REAL_TIME=`grep "real" $TESTCASE_RES | cut -f2`
  printf "%07.3fs  @  " $TESTCASE_REAL_TIME

  if [ $INFER_RESULT_CODE == 124 ] || [ $INFER_RESULT_CODE == 137 ] ; then
    echo -n "[TIMEOUT] " | tee -a $TESTCASE_RES
  fi

  show_status "(@ verify)"
  $VERIFY -i $TESTCASE_INV $TESTCASE | tee -a $TESTCASE_RES
  echo ""

  echo "$TESTCASE,`tail -n 1 $TESTCASE_RES`,$TESTCASE_REAL_TIME" >> "$CSV_SUMMARY"
done

print_counts () {
  while (( "$#" )) ; do
    echo -n "* $1 = " | tee -a "$TXT_SUMMARY"
    grep -e ",$2," "$CSV_SUMMARY" | wc -l | tee -a "$TXT_SUMMARY"
    shift ; shift
  done
}

echo ""
print_counts TOTAL_PASS ".*PASS.*" TOTAL_FAIL ".*FAIL.*"

echo "" | tee -a "$TXT_SUMMARY"
print_counts PASS "PASS" "PASS (NO SOLUTION)" "PASS (NO SOLUTION)" "[TIMEOUT] PASS (NO SOLUTION)" "\\[TIMEOUT\\] PASS (NO SOLUTION)"

echo "" | tee -a "$TXT_SUMMARY"
print_counts FAIL "FAIL {.*}" "FAIL (NO SOLUTION)" "FAIL (NO SOLUTION)" "[TIMEOUT] FAIL" "\\[TIMEOUT\\] FAIL {.*}" "[TIMEOUT] FAIL (NO SOLUTION)" "\\[TIMEOUT\\] FAIL (NO SOLUTION)"

echo -e "\nPASS Stats:" | tee -a "$TXT_SUMMARY"
awk -F',' '{
  if (NR == 1) { header = $3 ; next }
  if ($2 !~ /^PASS$/) { next }

  data[i++] = $3 ; sum += $3
  if (min == "") {
    min = max = $3
    min_file = max_file = $1
  }

  if ($3 > max) { max = $3 ; max_file = $1 }
  else if ($3 < min) { min = $3 ; min_file = $1 }
} END {
  printf "MIN(%s) = %0.3f  [%s]\n", header, min, min_file
  printf "MED(%s) = %0.3f\n", header, data[int((i-1)/2)]
  printf "AVG(%s) = %0.3f\n", header, sum/i
  printf "MAX(%s) = %0.3f  [%s]\n", header, max, max_file
  printf "SUM(%s) = %0.3f\n", header, sum
}' "$CSV_SUMMARY" | tee -a "$TXT_SUMMARY"

echo -e "\nA CSV summary has been saved to: $CSV_SUMMARY.\nA TXT summary has been saved to: $TXT_SUMMARY."