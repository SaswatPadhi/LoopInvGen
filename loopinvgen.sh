#!/usr/bin/env bash

set -Eumo pipefail

if (( ${BASH_VERSION%%.*} < 4 )); then echo "ERROR: [bash] version >= 4.0 required!" ; exit -1 ; fi

EXIT_CODE_BUILD_ERROR=-3
EXIT_CODE_USAGE_ERROR=-2

EXIT_CODE_PROCESS_ERROR=1
EXIT_CODE_RECORD_ERROR=2
EXIT_CODE_INFER_ERROR=3
EXIT_CODE_TIMEOUT=4

SELF_DIR="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"

BIN_DIR="$SELF_DIR/_build/install/default/bin"

PROCESS="$BIN_DIR/lig-process"
RECORD="$BIN_DIR/lig-record"
INFER="$BIN_DIR/lig-infer"
VERIFY="$BIN_DIR/lig-verify"

INVGAME_FEATURE_PARSER="$BIN_DIR/lig-tools-invgame-feature-parser"

if [ ! -f $PROCESS ] || [ ! -f $RECORD ] || [ ! -f $INFER ] || [ ! -f $VERIFY ]; then
  echo -en "
One or more dependencies not found. Building OCaml modules ...
" >&2 ; dune build || exit $EXIT_CODE_BUILD_ERROR
fi

trap 'jobs -p | xargs kill -TERM &> /dev/null' INT
trap "kill -KILL -`ps -o ppid= $$` &> /dev/null" QUIT TERM

SYGUS_EXT=".sl"

DO_CLEAN="no"
DO_VERIFY="no"

INTERMEDIATES_DIR="$SELF_DIR/_log"
declare -A DO_LOG
DO_LOG[process]=""
DO_LOG[record]=""
DO_LOG[infer]=""
DO_LOG[verify]=""
STATS_ARG=""
Z3_PATH="$SELF_DIR/_dep/z3"

EXPRESSIVENESS_LEVEL=6
INFER_TIMEOUT=86400
MIN_INFER_TIMEOUT=5
MIN_RECORD_STATES_PER_FORK=63
RECORD_TIMEOUT=0.5s
RECORD_FORKS=4
RECORD_STATES_PER_FORK=512

INVGAME_FEATURES_ARG=""
FEATURES_ARG=""
EXTRA_POS_STATES_PATH=""
EXTRA_NEG_STATES_ARG=""

PROCESS_ARGS=""
RECORD_ARGS=""
INFER_ARGS=""
VERIFY_ARGS=""

show_status() {
  printf "%s%16s" "$1" >&2
  printf %0"$(( ${#1} + 16 ))"d | tr 0 \\b >&2
}

usage() {
  if [ -n "$1" ]; then echo -e "\nERROR: $1" >&2 ; fi
  echo -en "
Usage: $0 [options] <path/to/benchmark.sl>

Flags:
    [--clean-intermediates, -c]
    [--verify, -v]

Configuration:
    [--intermediates-dir,     -i <path>]            (_log)
    [--log,                   -l <src>[,<src>...]]  ()\t\tsrc <- {process|record|infer|verify}
    [--stats-file,            -S <path>]            ()
    [--z3-exe-path,           -z <path>]            (_dep/z3)

Parameters:
    [--expressiveness-level,  -e <int>]             ($EXPRESSIVENESS_LEVEL)\t\t{1 = Eq .. 4 = Polyhedra .. 6 = Peano}
    [--max-states-per-fork,   -s <count>]           ($RECORD_STATES_PER_FORK)\t{> $MIN_RECORD_STATES_PER_FORK}
    [--infer-timeout,         -t <seconds>]         ($INFER_TIMEOUT)\t\t{> $MIN_INFER_TIMEOUT}

Optional Inputs:
    [--features-path,         -F <path>]            ()
    [--invgame-features-path, -f <path>]            ()
    [--extra-pos-states-path, -p <path>]            ()
    [--extra-neg-states-path, -n <path>]            ()

Arguments to Internal Programs (@ `dirname $RECORD`):
    [--Process-args,          -P \"<args>\"]          see \``basename "$PROCESS"` -h\` for details
    [--Record-args,           -R \"<args>\"]          see \``basename "$RECORD"` -h\` for details
    [--Infer-args,            -I \"<args>\"]          see \``basename "$INFER"` -h\` for details
    [--Verify-args,           -V \"<args>\"]          see \``basename "$VERIFY"` -h\` for details
" >&2 ; exit $EXIT_CODE_USAGE_ERROR
}

for opt in "$@"; do
  shift
  case "$opt" in
    "--clean-intermediates")   set -- "$@" "-c" ;;
    "--verify")                set -- "$@" "-v" ;;

    "--intermediates-path")    set -- "$@" "-i" ;;
    "--log")                   set -- "$@" "-l" ;;
    "--stats-file")            set -- "$@" "-S" ;;
    "--z3-exe-path")           set -- "$@" "-z" ;;

    "--expressiveness-level")  set -- "$@" "-e" ;;
    "--max-states-per-fork")   set -- "$@" "-s" ;;
    "--infer-timeout")         set -- "$@" "-t" ;;

    "--features-path")         set -- "$@" "-F" ;;
    "--invgame-features-path") set -- "$@" "-f" ;;
    "--extra-pos-states-path") set -- "$@" "-p" ;;
    "--extra-neg-states-path") set -- "$@" "-n" ;;

    "--Process-args")          set -- "$@" "-P" ;;
    "--Record-args")           set -- "$@" "-R" ;;
    "--Infer-args")            set -- "$@" "-I" ;;
    "--Verify-args")           set -- "$@" "-V" ;;

    "--")                      set -- "$@" "--" ;;
    "--"*)                     usage "Unrecognized option: $opt." ;;
    *)                         set -- "$@" "$opt"
  esac
done

OPTIND=1
while getopts ':cvi:l:S:z:e:s:t:f:F:P:R:I:V:' OPTION ; do
  case "$OPTION" in
    "c" ) DO_CLEAN="yes" ;;
    "v" ) DO_VERIFY="yes" ;;

    "i" ) INTERMEDIATES_DIR="$OPTARG"
          ;;
    "l" ) for LOG_SRC in `echo "$OPTARG" | tr ',' '\n' | sort -u | tr '\n' ' '` ; do
            case "$LOG_SRC" in
              process | record | infer | verify ) DO_LOG[$LOG_SRC]="yes" ;;
              * ) usage "Unknown source [$LOG_SRC] for logging."
            esac
          done
          ;;
    "S" ) [ -d "$OPTARG" ] && usage "Stats file [$OPTARG] is a directory!"
          [ -f "$OPTARG" ] && rm -rf $OPTARG
          STATS_ARG="-report-path $OPTARG"
          ;;
    "z" ) [ -f "$OPTARG" ] || usage "Z3 [$OPTARG] not found."
          Z3_PATH="$OPTARG"
          ;;

    "e" ) [ "$OPTARG" -ge "1" ] && [ "$OPTARG" -le "6" ] \
            || usage "The expressiveness level (= $OPTARG) must be between 1 and 6 (both inclusive)."
          EXPRESSIVENESS_LEVEL="$OPTARG"
          ;;
    "s" ) [ "$OPTARG" -gt "$MIN_RECORD_STATES_PER_FORK" ] \
            || usage "The number of states to record (= $OPTARG) must be > $MIN_RECORD_STATES_PER_FORK."
          RECORD_STATES_PER_FORK="$OPTARG"
          ;;
    "t" ) [ "$OPTARG" -gt "$MIN_INFER_TIMEOUT" ] \
            || usage "The inference timeout (= $OPTARG) must be > $MIN_INFER_TIMEOUT."
          INFER_TIMEOUT="$OPTARG"
          ;;

    "f" ) [ -f "$OPTARG" ] || usage "InvGame features file [$OPTARG] not found."
          INVGAME_FEATURES_ARG="$OPTARG"
          ;;
    "F" ) [ -f "$OPTARG" ] || usage "Features file [$OPTARG] not found."
          FEATURES_ARG="$OPTARG"
          ;;
    "p" ) [ -f "$OPTARG" ] || usage "Extra positive states file [$OPTARG] not found."
          EXTRA_POS_STATES_PATH="$OPTARG"
          ;;
    "n" ) [ -f "$OPTARG" ] || usage "Extra negative states file [$OPTARG] not found."
          EXTRA_NEG_STATES_ARG="-neg-states-path $OPTARG"
          ;;

    "P" ) PROCESS_ARGS="$OPTARG" ;;
    "R" ) RECORD_ARGS="$OPTARG" ;;
    "I" ) INFER_ARGS="$OPTARG" ;;
    "V" ) VERIFY_ARGS="$OPTARG" ;;

      * ) usage "Unrecognized option: -$OPTARG." ;;
  esac
done
shift $(($OPTIND -1))

[ -d "$INTERMEDIATES_DIR" ] || mkdir -p "$INTERMEDIATES_DIR"
[ -d "$INTERMEDIATES_DIR" ] \
  || usage "Intermediates directory [$INTERMEDIATES_DIR] not found."

[ "$#" -gt "0" ] || usage "No input file specified."
TESTCASE="$1"
[ -f "$TESTCASE" ] || usage "Input file [$TESTCASE] not found."

TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
TESTCASE_PREFIX="$INTERMEDIATES_DIR/$TESTCASE_NAME"

TESTCASE_FEATURES="$TESTCASE_PREFIX.feat"
TESTCASE_PROCESSED="$TESTCASE_PREFIX.bin"
TESTCASE_INVARIANT="$TESTCASE_PREFIX.inv"

TESTCASE_ALL_LOG="$TESTCASE_PREFIX.log"
TESTCASE_REC_LOG="$TESTCASE_PREFIX.rlog"

TESTCASE_REC_STATES="$TESTCASE_PREFIX.rstates"
TESTCASE_ALL_STATES="$TESTCASE_PREFIX.states"

PROCESS="$PROCESS -z $Z3_PATH"
RECORD="$RECORD -z $Z3_PATH"
INFER="$INFER -z $Z3_PATH"
VERIFY="$VERIFY -z $Z3_PATH"

INFER_TIMEOUT="${INFER_TIMEOUT}s"

rm -rf "$TESTCASE_REC_STATES"* "$TESTCASE_ALL_STATES" \
       "$TESTCASE_ALL_LOG" "$TESTCASE_INVARIANT"
echo > "$TESTCASE_FEATURES"

[ -z "${DO_LOG[process]}" ] || DO_LOG[process]="-l $TESTCASE_ALL_LOG"
[ -z "${DO_LOG[record]}" ] || DO_LOG[record]="-l $TESTCASE_REC_LOG"
[ -z "${DO_LOG[infer]}" ] || DO_LOG[infer]="-l $TESTCASE_ALL_LOG"
[ -z "${DO_LOG[verify]}" ] || DO_LOG[verify]="-l $TESTCASE_ALL_LOG"

#
# LoopInvGen Stages
#

show_status "(processsing)"

(
  if [ -n "$INVGAME_FEATURES_ARG" ]; then
    $INVGAME_FEATURE_PARSER "$INVGAME_FEATURES_ARG" | sort -u -o "$TESTCASE_FEATURES"
  fi
  cat "$FEATURES_ARG" "$TESTCASE_FEATURES" 2> /dev/null | sort -u -o "$TESTCASE_FEATURES"
) &

$PROCESS -o "$TESTCASE_PROCESSED" ${DO_LOG[process]} $PROCESS_ARGS \
         "$TESTCASE" > "$TESTCASE_INVARIANT"
[ $? == 0 ] || exit $EXIT_CODE_PROCESS_ERROR

if [ -s "$TESTCASE_INVARIANT" ]; then
  INFER_RESULT_CODE=0
else
  show_status "(recording)"

  LOG_PARAM=""
  for i in `seq 1 $RECORD_FORKS` ; do
    [ -z "${DO_LOG[record]}" ] || LOG_PARAM="${DO_LOG[record]}$i"
    (timeout $RECORD_TIMEOUT \
             $RECORD -s $RECORD_STATES_PER_FORK -r "seed$i" $LOG_PARAM $RECORD_ARGS \
                     "$TESTCASE_PROCESSED") > "$TESTCASE_REC_STATES$i" &
  done
  wait

  grep -hsv "^[[:space:]]*$" "$TESTCASE_REC_STATES"* "$EXTRA_POS_STATES_PATH" | sort -u > "$TESTCASE_ALL_STATES"
  [ -z "${DO_LOG[record]}" ] || cat "$TESTCASE_REC_LOG"* >> "$TESTCASE_ALL_LOG" 2> /dev/null || true

  show_status "(inferring)"

  timeout --foreground $INFER_TIMEOUT \
          $INFER -s "$TESTCASE_ALL_STATES" -max-expressiveness-level "$EXPRESSIVENESS_LEVEL"         \
                 -features-path $TESTCASE_FEATURES $STATS_ARG $EXTRA_NEG_STATES_ARG ${DO_LOG[infer]} \
                 $INFER_ARGS "$TESTCASE_PROCESSED" > "$TESTCASE_INVARIANT"
  INFER_RESULT_CODE=$?
fi

if [ "$DO_VERIFY" = "yes" ]; then
  if [ $INFER_RESULT_CODE == 124 ] || [ $INFER_RESULT_CODE == 137 ]; then
    echo > "$TESTCASE_INVARIANT" ; echo -n "[TIMEOUT] "
  fi

  show_status "(verifying)"

  $VERIFY -s "$TESTCASE" ${DO_LOG[verify]} $VERIFY_ARGS "$TESTCASE_INVARIANT" \
    > "$TESTCASE_PREFIX.result"
  RESULT_CODE=$?

  show_status "" ; cat "$TESTCASE_PREFIX.result"
elif [ $INFER_RESULT_CODE == 0 ]; then
  cat "$TESTCASE_INVARIANT" ; echo
  RESULT_CODE=0
else
  show_status "(fail)"
  RESULT_CODE=$EXIT_CODE_INFER_ERROR
  if [ $INFER_RESULT_CODE == 124 ] || [ $INFER_RESULT_CODE == 137 ]; then
    RESULT_CODE=$EXIT_CODE_TIMEOUT
  fi
  echo ""
fi


if [ "$DO_CLEAN" == "yes" ]; then
  rm -rf "$TESTCASE_REC_STATES"* "$TESTCASE_REC_LOG"*
  if [ $RESULT_CODE == 0 ] || [ $RESULT_CODE == 2 ]; then
    rm -rf "$TESTCASE_PROCESSED" "$TESTCASE_ALL_STATES"
  fi
fi

exit $RESULT_CODE