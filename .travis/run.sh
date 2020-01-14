#!/usr/bin/env bash

#
# Because the ocaml/opam2 docker image uses a stale
# local copy of opam repo, we just delete everything
# and start from scratch :)
#
rm -rf ~/.opam

opam init --compiler="${OCAML_VERSION}"
opam update

eval `opam env`
opam config report

if [ -z "${MIN_REQS_ONLY}" ]; then
    opam install --yes --deps-only --with-test ./LoopInvGen.opam
else
    opam install --yes alcotest.0.8.0   \
                       core.v0.13.0     \
                       dune.1.6.0       \
                       ppx_let.v0.13.0
fi

opam list
pwd ; ls -lah

### TODO: Need z3 to actually run the tests

dune build --verbose
dune build test/Runner.exe --verbose
dune build app/App.exe --verbose