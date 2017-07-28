#!/usr/bin/env bash

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

opam pin add LoopInvGen . --no-action --yes --kind=path
opam install LoopInvGen --deps-only

RC=$?
if [ $RC -ne 0 ]; then
    # Try again after updating the environment (bin path)
    eval `opam config env --shell=bash`
    opam install LoopInvGen --deps-only
fi

oasis setup -setup-update dynamic
./configure ${LIG_DEBUG_FLAG:- --disable-debug}     \
            ${LIG_DOCS_FLAG:- --disable-docs}       \
            ${LIG_PROFILE_FLAG:- --disable-profile} \
            ${LIG_TESTS_FLAG:- --disable-tests}
make