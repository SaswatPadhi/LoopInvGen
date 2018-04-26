#!/usr/bin/env bash

### Initialize `opam`

export OPAMYES=1

if [ -f "$HOME/.opam/config" ]; then
    opam update || UPDATE_FAILED="yes"
    opam upgrade || UPGRADE_FAILED="yes"
    if [ -n "$UPDATE_FAILED" -o -n "$UPGRADE_FAILED" ]; then
        # Something went wrong, restart from scratch
        rm -rf "$HOME/.opam/"
        opam init
    fi
else
    opam init
fi

if [ -n "${OCAML_VERSION}" ]; then
    opam switch ${OCAML_VERSION}
fi
eval `opam config env --shell=bash`

opam config report

### Pin `LoopInvGen` package, install deps

opam pin add LoopInvGen . --no-action --yes --kind=path
opam install LoopInvGen --deps-only --verbose


### Check installation status and build

RC=$?
if [ $RC -ne 0 ]; then
    # Try again after updating the environment (bin path)
    eval `opam config env --shell=bash`
    opam install LoopInvGen --deps-only
fi

jbuilder build -f @debug

BUILD_FLAGS=($BUILD_FLAGS)
for flag in $BUILD_FLAGS ; do
    if [ "$flag" = "-optimize" ]; then
        jbuilder build -f @optimize
    elif [ "$flag" = "-debug" ]; then
        jbuilder build -f @debug
    fi
done

jbuilder build --verbose