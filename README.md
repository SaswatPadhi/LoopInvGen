# LoopInvGen [![Build Status](https://travis-ci.org/SaswatPadhi/LoopInvGen.svg?branch=master)](https://travis-ci.org/SaswatPadhi/LoopInvGen)

A loop invariant generator.

## Installation

#### 1. Install `ocaml` >= 4.04.2.
It is recommended to use an OCaml compiler with `flambda` optimizations enabled.
For example, with [`opam`](https://opam.ocaml.org/), you could run `opam install 4.06.0+flambda`.

#### 2. Install (for example, using `opam install`) the following packages:
```
  "alcotest"      {>= "0.7"}
  "core"          {>= "0.10"}
  "core_extended" {>= "0.10"}
  "oasis"         {>= "0.4"}
```

#### 3. Run `./create-package.sh -z /PATH/TO/z3`.
The `create-package.sh` script would build Z3, copy it to `./_dep/`, and then build LoopInvGen.
Alternatively, you can copy a precompiled version of Z3 to `./_dep/`, and simply run `./create-package.sh`.

For future builds after any chances to the source code, you only need to `make`.

## Testing

Execute `./benchmarks/run_all.sh` to run all the tests (SyGuS benchmarks from previous years).

## Usage

Run `./loopinvgen.sh /path/to/sygus.sl` to infer the loop invariant for the SuGuS test case `sygus.sl`.
