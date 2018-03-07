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

oasis setup -setup-update dynamic

./configure ${DEBUG_FLAG:- --disable-debug}     \
            ${DOCS_FLAG:- --disable-docs}       \
            ${PROFILE_FLAG:- --disable-profile} \
            ${TESTS_FLAG:- --disable-tests}     \
            ${BUILD_FLAGS}

make clean ; make