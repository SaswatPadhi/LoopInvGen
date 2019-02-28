#!/usr/bin/env bash

ROOT="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"

CHANGED="`bash $ROOT/check.sh ; echo $?`"
if [ "$CHANGED" -eq "0" ]; then
    echo "Skipping build since no source files have been modified."
else
    docker exec -t \
                -e OCAML_VERSION="$OCAML_VERSION" \
                -e PROFILE="$PROFILE" \
                -e MIN_REQS_ONLY="$MIN_REQS_ONLY" \
                ocaml bash -c "cd /LoopInvGen && bash -ex .travis/run.sh"
fi