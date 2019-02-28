#!/usr/bin/env bash

set -eou pipefail

ROOT="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"

CHANGED="`bash $ROOT/check.sh ; echo $?`"
if [ "$CHANGED" -eq "0" ]; then
    echo "Skipping `docker` installation since no source files have been modified."
else
    docker run --name ocaml -td ocaml/opam2
    docker exec ocaml bash -c "sudo apt -yqq install m4"
    docker cp "$ROOT/.." ocaml:/LoopInvGen
    docker exec ocaml bash -c "sudo chown -R opam:opam /LoopInvGen"
fi