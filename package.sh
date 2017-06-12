#!/bin/bash

make clean && make

rm -rf bin && mkdir -p bin

cp _dep/z3.bin bin/z3
cp _build/src/Record.native \
   _build/src/Infer.native  \
   _build/src/Check.native  \
   verify.sh                \
   bin

cat <<EOF > bin/starexec_run_LoopInvGen
#!/bin/bash

./verify.sh -i "." -z "./z3" "\$1"
EOF
chmod +x bin/starexec_run_LoopInvGen

cat <<EOF > starexec_description.txt
A loop invariant inference tool built using PIE: precondition inference engine.

https://github.com/SaswatPadhi/SyGuS.PIE
EOF

tar cvzf PIE_s_INV.tgz bin
rm -rf bin