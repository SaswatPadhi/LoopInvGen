#!/bin/bash

usage() {
  echo "
Usage: $0 [flags]

Flags:
    [--make-z3, -z]
" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :z: --long make-z3 -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

MAKE_Z3=""
while true ; do
  case "$1" in
    -z | --make-z3 )
         MAKE_Z3="$2" ;
         shift ; shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

if [ -n "$MAKE_Z3" ] ; then
  LIG=`pwd`
  cd "$MAKE_Z3"
  #LDFLAGS="-static-libstdc++ -static-libgcc -static" \
  #CXXFLAGS="-static-libstdc++ -static-libgcc -static" \
  #python2 scripts/mk_make.py
  cd build
  make -j4
  mkdir -p "$LIG/_dep"
  cp z3 "$LIG/_dep/z3.bin"
  cd "$LIG"
fi

oasis setup -setup-update dynamic

make clean

./configure --disable-debug --disable-profile \
            --disable-tests --disable-docs
make

rm -rf bin && mkdir -p bin

cp _dep/z3.bin bin/z3
cp _build/src/Record.native \
   _build/src/Infer.native  \
   _build/src/Check.native \
   loopinvgen.sh            \
   bin

cat <<EOF > bin/starexec_run_default
#!/bin/bash

./loopinvgen.sh -t 36000 -i "." -z "./z3" "\$1"
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