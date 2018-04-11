# LoopInvGen [![Build Status](https://travis-ci.org/SaswatPadhi/LoopInvGen.svg?branch=master)][travis]

A loop invariant generator.


## Installation

### Using `Dockerfile`

_**Note:** The docker image consumes > 4GB of disk space._

1. Build a docker image: `docker build -t LoopInvGen github.com/SaswatPadhi/LoopInvGen`
2. Run a container over the image: `docker run -ti LoopInvGen`

This would give you a `bash` shell within LoopInvGen directory.


### Manual Installation

#### 1. Install `ocaml` >= 4.04.2.
It is recommended to use an OCaml compiler with [`flambda`][flambda] optimizations enabled.
For example, with [`opam`](https://opam.ocaml.org/), you could:
- run `opam switch 4.06.1+flambda` for opam 1.x
- run `opam switch create 4.06.1+flambda` for opam 2.x

#### 2. Install (for example, using `opam install`) the following packages:
```
  "core"          {>= "0.11"}
  "core_extended" {>= "0.11"}
  "jbuilder"      {>= "1.0+beta19"}
```

#### 3. `git checkout` the [Z3 project][z3].

#### 4. Run `./create-package.sh -z /PATH/TO/z3`.
The `create-package.sh` script would build Z3, copy it to `./_dep/`, and then build LoopInvGen.
Alternatively, you can copy a precompiled version of Z3 to `./_dep/`, and simply run `./create-package.sh`.

For future builds after any chances to the source code, you only need to run `jbuilder build`.

You can also configure the build mode to either `fast-compile` (default) or `optimize`, using: `jbuilder build @<mode>`.
(You would need to run `jbuilder build` after changing the build mode.)


## Testing

Execute `./benchmarks/run_all.sh -i` to run all the tests (SyGuS benchmarks from previous years).


## Usage

Run `./loopinvgen.sh /path/to/sygus.sl` to infer the loop invariant for the SuGuS test case `sygus.sl`.




[flambda]: https://caml.inria.fr/pub/docs/manual-ocaml/flambda.html
[travis]:  https://travis-ci.org/SaswatPadhi/LoopInvGen
[z3]:      https://github.com/Z3Prover/z3
