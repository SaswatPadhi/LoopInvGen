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

jbuilder build -f @fast-compile
while true ; do
  case "$1" in
    -z | --make-z3 )
         MAKE_Z3="$2" ;
         shift ; shift ;;
    -j | --jobs )
         JOBS="$2" ;
         shift ; shift ;;
    -O | --optimize )
         jbuilder build -f @optimize
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
  cp z3 "$LIG/_dep/z3"
  cd "$LIG"
fi

jbuilder build @local -p LoopInvGen -j "$JOBS"

rm -rf starexec && mkdir -p starexec/bin

cp -rL _bin _dep loopinvgen.sh starexec/bin

cat <<EOF > starexec/bin/starexec_run_default
#!/bin/bash

./loopinvgen.sh -t 36000 -p "." -z "_dep/z3" "\$1"
EOF
chmod +x starexec/bin/starexec_run_default

cat <<EOF > starexec/bin/starexec_run_debug
#!/bin/bash

pwd
ls -lah

file _dep/z3 _bin/lig-record _bin/lig-infer _bin/lig-verify
ldd _dep/z3 _bin/lig-record _bin/lig-infer _bin/lig-verify

_dep/z3
_bin/lig-record -h
_bin/lig-infer -h
_bin/lig-verify -h
EOF
chmod +x starexec/bin/starexec_run_debug

cat <<EOF > starexec/starexec_description.txt
A loop invariant inference tool built using PIE: precondition inference engine.

https://github.com/SaswatPadhi/LoopInvGen
EOF

chmod -R 777 starexec/bin

echo -ne "\nPreparing starexec package (starexec/):\n"
cd starexec
tar cvzf ../LoopInvGen_SyGuS_INV.tgz ./*
#rm -rf starexec