#!/usr/bin/env bash

### Initialize `opam`

export OPAMYES=1

if [ -f "$HOME/.opam/config" ]; then
    opam update || UPDATE_FAILED="yes"
    opam upgrade || UPGRADE_FAILED="yes"
    if [ -n "$UPDATE_FAILED" -o -n "$UPGRADE_FAILED" ]; then
        # Something went wrong, restart from scratch
        rm -rf "$HOME/.opam/"
        opam init --bare
    fi
else
    opam init --bare
fi

if [ -n "${OCAML_VERSION}" ]; then
    opam switch set ${OCAML_VERSION} || opam switch create ${OCAML_VERSION}
fi
eval `opam config env`

opam config report


### Pin `LoopInvGen` package, install deps

opam pin add LoopInvGen . --no-action --yes --kind=path
opam install LoopInvGen --deps-only  --with-test

opam list
ls -lah


### Build LoopInvGen and test runner
### TODO: Need z3 to actually run the tests

dune build --verbose --profile $PROFILE
dune build test/Runner.exe --verbose --profile $PROFILE