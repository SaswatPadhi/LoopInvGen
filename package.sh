#!/bin/bash

make clean && make

mkdir -p bin/_dep
mkdir bin/_logs

cp _dep/z3.bin bin/_dep
cp _build/src/Recorder.native \
   _build/src/Verifier.native \
   bin
cp verify.sh bin/starexec_run_s_INV

tar cvzf PIE_s_INV.tgz bin
rm -rf bin