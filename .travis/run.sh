#!/usr/bin/env bash

### Initialize `opam`

export OPAMYES=1

opam init --compiler="${OCAML_VERSION}"
eval `opam env`

opam update
opam config report


### Pin `LoopInvGen` package and install deps

opam pin add LoopInvGen . --no-action --yes --kind=path

if [ -z "${MIN_REQS_ONLY}" ]; then
    opam install LoopInvGen --deps-only --with-test
else
    opam install --yes alcotest.0.8.0 core.v0.12.2 dune.1.6.0 ppx_let.v0.12.0
fi

opam list
ls -lah


### Build LoopInvGen and test runner
### TODO: Need z3 to actually run the tests

dune build --verbose
dune build test/Runner.exe --verbose
