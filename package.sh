#!/bin/bash

make clean

./configure --disable-debug --disable-profile \
            --disable-tests --disable-docs
make

rm -rf bin && mkdir -p bin

cp _dep/z3.bin bin/z3
cp _build/src/Record.native \
   _build/src/Infer.native  \
   _build/src/Check.native  \
   verify.sh                \
   bin

cat <<EOF > bin/starexec_run_default
#!/bin/bash

./verify.sh -t 36000 -i "." -z "./z3" "\$1"
EOF
chmod +x bin/starexec_run_default

cat <<EOF > bin/starexec_run_debug
#!/bin/bash

pwd
ls -lah
file z3 Record.native Infer.native Check.native
ldd z3 Record.native Infer.native Check.native
./z3
./Record.native
EOF
chmod +x bin/starexec_run_debug

cat <<EOF > starexec_description.txt
A loop invariant inference tool built using PIE: precondition inference engine.

https://github.com/SaswatPadhi/LoopInvGen
EOF

chmod -R 777 bin
CONTENTS="bin starexec_description.txt"

tar cvzf LoopInvGen_SyGuS_INV.tgz $CONTENTS
rm -rf $CONTENTS