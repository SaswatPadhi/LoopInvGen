#!/bin/bash

usage() {
  echo "
Usage: $0 [flags]

Flags:
    [--optimize, -O]        Optimize for speed (build takes MUCH longer!)

Configuration:
    [--make-z3, -z <path>]  Also build a specialized version of `z3`
    [--jobs, -j <num>]      Use <num> jobs in `make`
" 1>&2 ;
  exit 1 ;
}

OPTS=`getopt -n 'parse-options' -o :Oz:j: --long optimize,make-z3:,jobs: -- "$@"`
if [ $? != 0 ] ; then usage ; fi

eval set -- "$OPTS"

JOBS="4"
MAKE_Z3=""
OPTIMIZE=""

while true ; do
  case "$1" in
    -z | --make-z3 )
         MAKE_Z3="$2" ;
         shift ; shift ;;
    -j | --jobs )
         JOBS="$2" ;
         shift ; shift ;;
    -O | --optimize )
         OPTIMIZE="--enable-optimize" ;
         shift ;;
    -- ) shift; break ;;
    * ) break ;;
  esac
done

if [ -n "$MAKE_Z3" ] ; then
  LIG=`pwd`
  Z3_BUILD_DIR="build_for_pie"
  cd "$MAKE_Z3"

  rm -rf "$Z3_BUILD_DIR"
  mkdir -p "$Z3_BUILD_DIR"

  python2 scripts/mk_make.py --staticbin --staticlib \
                             --build "$Z3_BUILD_DIR"

  cd "$Z3_BUILD_DIR"
  make -j "$JOBS"

  mkdir -p "$LIG/_dep"
  cp z3 "$LIG/_dep/z3.bin"
  cd "$LIG"
fi

oasis setup -setup-update dynamic

make distclean

./configure --disable-debug --disable-profile \
            --disable-tests --disable-docs \
            $OPTIMIZE
make -j "$JOBS"

rm -rf bin && mkdir -p bin

cp _dep/z3.bin bin/z3
cp _build/src/Record.native \
   _build/src/Infer.native  \
   _build/src/Verify.native \
   loopinvgen.sh            \
   bin

cat <<EOF > bin/starexec_run_default
#!/bin/bash

./loopinvgen.sh -t 36000 -p "." -z "./z3" "\$1"
EOF
chmod +x bin/starexec_run_default

cat <<EOF > bin/starexec_run_debug
#!/bin/bash

pwd
ls -lah
file z3 Record.native Infer.native Verify.native
ldd z3 Record.native Infer.native Verify.native
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