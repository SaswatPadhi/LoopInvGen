#!/bin/bash

if (( ${BASH_VERSION%%.*} < 4 )) ; then echo "ERROR: [bash] version 4.0+ required!" ; exit -1 ; fi

SELF_DIR="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"

trap 'kill -TERM -$INFER_PID > /dev/null 2> /dev/null' INT
trap "kill -KILL -`ps -o pgid= $$` > /dev/null 2> /dev/null" QUIT TERM

SYGUS_EXT=".sl"
RESULT_EXT=".res"
RERUN_PASSED=""
REVERIFY_FAILED=""

SKIP_MARK="[SKIPPED] "
CONTINUE_FROM="1"
BENCHMARKS_DIR=""
LOGS_DIR="$SELF_DIR/_log"
Z3_PATH="$SELF_DIR/_dep/z3"

TIMEOUT="60"
TOOL="$SELF_DIR/loopinvgen.sh"
VERIFY="$SELF_DIR/_build/install/default/bin/lig-verify"
VERIFY_ARGS=""

show_status() {
  printf "%s%16s" "$1" >&2
  printf %0"$(( ${#1} + 16 ))"d | tr 0 \\b >&2
}

usage() {
  if [ -n "$1" ] ; then echo -e "\nERROR: $1" >&2 ; fi
  echo -en "
Usage: $0 [options] -b <benchmarks_path> -- [tool specific options]

Flags:
    [--rerun-passed, -r]
    [--reverify-failed, -y]
    [--no-skipped-mark, -s]

Configuration:
    --benchmarks, -b <path>
    [--continue-from, -c <int>]       ($CONTINUE_FROM)
    [--logs-dir, -l <path>]           ($LOGS_DIR)
    [--time-out, -t <seconds>]        ($TIMEOUT)
    [--tool, -T <path>]               ($TOOL)
    [--z3-path, -z <path>]            ($Z3_PATH)

Arguments to Internal Programs (@ `dirname $VERIFY`):
    [--Verify-args, -V \"<args>\"]    see \``basename "$VERIFY"` -h\` for details
" 1>&2 ; exit -1
}

OPTS=`getopt -n 'parse-options' -o :b:c:l:t:rsT:V:yz: --long benchmarks:,continue-from:,logs-dir:,time-out:,rerun-passed,no-skipped-mark,tool:,Verify-args:,reverify-failed,z3-path: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

while true ; do
  case "$1" in
    -b | --benchmarks )
         [ -d "$2" ] || usage "Benchmarks directory [$2] not found."
         BENCHMARKS_DIR="`realpath "$2"`"
         shift ; shift ;;
    -c | --continue-from )
         [ "$2" -gt "0" ] || usage "$2 is not a positive index.."
         CONTINUE_FROM="$2"
         shift ; shift ;;
    -l | --logs-dir )
         LOGS_DIR="`realpath "$2"`"
         shift ; shift ;;
    -t | --time-out )
         TIMEOUT="$2"
         shift ; shift ;;
    -r | --rerun-passed )
         RERUN_PASSED="YES"
         shift ;;
    -s | --no-skipped-mark )
         SKIP_MARK=""
         shift ;;
    -T | --tool )
         [ -f "$2" ] || usage "Tool [$2] not found."
         TOOL="$2"
         shift ; shift ;;
    -V | --Verify-args )
         VERIFY_ARGS="$2"
         shift ; shift ;;
    -y | --reverify-failed )
         REVERIFY_FAILED="YES"
         shift ;;
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

mkdir -p "$LOGS_DIR"

cd "`dirname "$TOOL"`"
TOOL="./`basename "$TOOL"`"

CSV_SUMMARY="$LOGS_DIR/summary.csv"
TXT_SUMMARY="$LOGS_DIR/summary.txt"

echo -n "" > "$TXT_SUMMARY"
echo "Benchmark,Verdict,Wall_Time(s),Max_Memory(MB)" > "$CSV_SUMMARY"

COUNTER=0
for TESTCASE in `find "$BENCHMARKS_DIR" -name *$SYGUS_EXT` ; do
  TESTCASE_NAME=${TESTCASE#$BENCHMARKS_DIR/}
  TESTCASE_NAME=${TESTCASE_NAME%$SYGUS_EXT}
  TESTCASE_PREFIX="$LOGS_DIR/$TESTCASE_NAME.t_all"

  mkdir -p "`dirname \"$TESTCASE_PREFIX\"`"

  TESTCASE_RES="$TESTCASE_PREFIX$RESULT_EXT"
  TESTCASE_INV="$TESTCASE_PREFIX.inv"

  (( COUNTER++ ))
  printf "[%4d] %72s => " $COUNTER $TESTCASE_NAME

  if [ -f "$TESTCASE_RES" ]; then
    OLD_VERDICT=`tail -n 1 $TESTCASE_RES`
  fi

  if [ "$CONTINUE_FROM" -gt "$COUNTER" ] || ( \
       [ -z "$RERUN_PASSED" ] && [ -f "$TESTCASE_RES" ] && [[ "$OLD_VERDICT" =~ .*PASS.* ]] \
     ); then
    TESTCASE_REAL_TIME=`grep "real(s)" $TESTCASE_RES | cut -f2`
    TESTCASE_MAX_MEMORY=`grep "rss(kb)" $TESTCASE_RES | cut -f2`
    TESTCASE_MAX_MEMORY=$(( TESTCASE_MAX_MEMORY / 1024 ))
    printf "%8.3fs [%5.0f MB]  @  $SKIP_MARK$OLD_VERDICT\n" $TESTCASE_REAL_TIME $TESTCASE_MAX_MEMORY
    echo "$TESTCASE,$OLD_VERDICT,$TESTCASE_REAL_TIME,$TESTCASE_MAX_MEMORY" >> "$CSV_SUMMARY"
    continue
  fi

  if [ -z "$REVERIFY_FAILED" ] || [ ! -f "$TESTCASE_INV" ]; then
    echo > $TESTCASE_INV ; echo > $TESTCASE_RES

    show_status "(inferring)"
    (\time --format "\nreal(s)\t%e\nuser(s)\t%U\n sys(s)\t%S\n   cpu%%\t%P\nrss(kb)\t%M\n" \
          timeout $TIMEOUT $TOOL $TESTCASE $TOOL_ARGS) > $TESTCASE_INV 2> $TESTCASE_RES &
    INFER_PID=$!
    wait $INFER_PID
    INFER_RESULT_CODE=$?

    if [ $INFER_RESULT_CODE == 124 ] || [ $INFER_RESULT_CODE == 137 ] ; then
      echo -n "[TIMEOUT] " >> $TESTCASE_RES
    fi
  else
    head -n -1 "$TESTCASE_RES" > /tmp/tmp ; mv /tmp/tmp "$TESTCASE_RES"
    if [[ "$OLD_VERDICT" =~ .*TIMEOUT.* ]]; then
      echo -n "[TIMEOUT] " >> $TESTCASE_RES
    fi
  fi

  TESTCASE_REAL_TIME=`grep "real(s)" $TESTCASE_RES | cut -f2`
  TESTCASE_MAX_MEMORY=`grep "rss(kb)" $TESTCASE_RES | cut -f2`
  TESTCASE_MAX_MEMORY=$(( TESTCASE_MAX_MEMORY / 1024 ))
  printf "%8.3fs [%5.0f MB]  @  " $TESTCASE_REAL_TIME $TESTCASE_MAX_MEMORY

  show_status "(verifying)"
  RESULT_CODE=0
  timeout 300 $VERIFY -s $TESTCASE $VERIFY_ARGS $TESTCASE_INV >> $TESTCASE_RES
  RESULT_CODE=$?
  if [ $RESULT_CODE == 124 ] || [ $RESULT_CODE == 137 ]; then
    echo "PASS (UNVERIFIED)" >> $TESTCASE_RES
  fi
  show_status "" ; tail -n 1 $TESTCASE_RES ; echo ""

  echo "$TESTCASE,`tail -n 1 $TESTCASE_RES`,$TESTCASE_REAL_TIME,$TESTCASE_MAX_MEMORY" >> "$CSV_SUMMARY"
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
print_counts PASS "PASS" "PASS (NO SOLUTION)" "PASS (NO SOLUTION)" "[TIMEOUT] PASS (NO SOLUTION)" "\\[TIMEOUT\\] PASS (NO SOLUTION)" "PASS (UNVERIFIED)"

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
