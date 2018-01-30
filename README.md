# LoopInvGen

A loop invariant generator.

## Installation

1. Please `opam install` the following packages:
```
  "alcotest"      {>= "0.7"}
  "core"          {>= "0.10"}
  "core_extended" {>= "0.10"}
  "oasis"         {>= "0.4"}
```

2. Run, `./create-package.sh -z /PATH/TO/Z3`.
The `create-package.sh` script would build Z3, copy it to `./_dep/`, and then build LoopInvGen.

Alternatively, you can copy a precompiled version of Z3 to `./dep/` and run `./create-package.sh`.

## Testing

Execute `./benchmarks/run_all.sh` to run all the tests (SyGuS benchmarks from previous years).

## Usage

Run `./loopinvgen.sh /path/to/sygus.sl` to infer the loop invariant for the SuGuS test case `sygus.sl`.