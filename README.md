# LoopInvGen [![Build Status](https://travis-ci.org/SaswatPadhi/LoopInvGen.svg?branch=master)][travis]

A data-driven tool that uses automatic feature synthesis to generate provably-sufficient loop invariants for program verification.

<p align="center"><img src="docs/architecture.png" width="400"/></p>

#### :page_with_curl: Papers and Presentations

- [SyGuS-COMP 2017][SyGuSCOMP17] (in conjunction with CAV and SYNT 2017) -
  Solver [Presentation](docs/2017_SyGuS-COMP-Presentation.pdf) and [Description](docs/2017_SyGuS-COMP-Description.pdf)
- [PLDI 2016](http://conf.researchr.org/home/pldi-2016) -
  Original [paper on PIE](http://saswatpadhi.github.io/assets/pdf/pldi2016_pie.pdf) (Precondition Inference Engine), the backbone of LoopInvGen

#### :trophy: Awards and Honors

- :1st_place_medal: [SyGuS-COMP 2017][SyGuSCOMP17] - INV Track **Winner** ([Results](http://sygus.seas.upenn.edu/files/sygus-comp17_results.pdf))

## Installation

### Using `Dockerfile` (recommended)

_**Note:** The docker image consumes ~4GB of disk space._

We recommend running LoopInvGen within a docker container,
as opposed to installing it within your host OS.
Docker containers have negligible performance overhead.
(See [this report](http://domino.research.ibm.com/library/cyberdig.nsf/papers/0929052195DD819C85257D2300681E7B/$File/rc25482.pdf))

0. [Get `docker` for your OS](https://docs.docker.com/install).
1. Build our docker image: `docker build -t loopinvgen github.com/SaswatPadhi/LoopInvGen`.
2. Run a container over the image: `docker run -it loopinvgen`. This would give you a `bash` shell within LoopInvGen directory.

You may also limit the container's memory and/or CPU usage:
```bash
# Create a LoopInvGen container with 4GB memory, no swap and 1 CPU
$ docker run -it --memory=4g --memory-swap=4g --cpus=1 loopinvgen
```

See [the official Docker guide](https://docs.docker.com/config/containers/resource_constraints)
for more details on applying resource constraints.



### Manual Installation

<details>

<summary><kbd>CLICK</kbd> to reveal instructions</summary>

#### 0. Get the required packages for your OS.

Please see the [`Dockerfile`](Dockerfile#L19-L21) for the complete list of required packages
for building LoopInvGen and its dependencies.  
Most of these packages are already installed on standard installations of most *nix distributions,
except, may be, these: `aspcud libgmp-dev libomp-dev m4`.

#### 1. Install `ocaml` >= 4.04.2.
We recommend using an OCaml compiler with [`flambda`][flambda] optimizations enabled.
For example, with [`opam`](https://opam.ocaml.org/), you could:
- run `opam switch 4.06.1+flambda` for opam 1.x
- run `opam switch create 4.06.1+flambda` for opam 2.x

#### 2. `opam install` the dependencies.
```bash
$ opam install alcotest.0.8.3 core.v0.11.0 core_extended.v0.11.0 jbuilder.1.0+beta20
```

#### 3. Get the [Z3 project][z3].
We have tested LoopInvGen with the latest stable version of Z3 (4.6.0).
You could either:
- `git checkout https://github.com/Z3Prover/z3.git` for the bleeding edge version, or
- `wget https://github.com/Z3Prover/z3/archive/z3-4.6.0.zip && unzip z3-4.6.0.zip` for the stable version

#### 4. `git clone` this project, and build everything.
```bash
$ ./build_all.sh -z /PATH/TO/z3_dir
```
The `build_all.sh` script would build Z3, copy it to `./_dep/`, and then build LoopInvGen.
Alternatively, you can copy a precompiled version of Z3 to `./_dep/`, and simply run `./build_all.sh`.

For debug builds, use the `-D` or `--debug` switch when invoking `./build_all.sh`.

For future builds after any changes to the source code, you only need to run `jbuilder build`.
You can configure the build mode to either `debug` (default) or `optimize`,
using: `jbuilder build @<mode>`.  
(You would need to run `jbuilder build` after changing the build mode.)

</details>

## Usage

Infer invariants for SyGuS benchmarks by invoking LoopInvGen as:
```bash
$ ./loopinvgen.sh benchmarks/2016/array.sl
(define-fun inv-f ((x Int) (y Int) (z Int)) Bool (not (and (>= x 5) (not (<= y z)))))
```

**Note:** LoopInvGen processes benchmarks in multiple stages.
We trap <kbd>CTRL</kbd>+<kbd>C</kbd> (`SIGINT` signal) to break out of the current stage,
and <kbd>CTRL</kbd>+<kbd>\\</kbd> (`SIGQUIT` signal) to kill LoopInvGen and with its child processes.

#### Inference Timeout

The `-t` flag allows users to run LoopInvGen with a maximum limit
on the number of _seconds_ (wall-clock time) for which the inference algorithm may run.
```bash
$ ./loopinvgen.sh -t 8 benchmarks/2016/array.sl
```

For timeout based on CPU time, you may use [`ulimit`](https://ss64.com/bash/ulimit.html).

<details>

#### Verifying Generated Invariants

The `-v` switch makes LoopInvGen verify the generated invariant:
```bash
$ ./loopinvgen.sh -v benchmarks/2016/array.sl
PASS
```

It gives one of the following verdicts:
```
PASS                : The generated invariant successfully verifies the benchmark.
PASS (NO SOLUTION)  : The benchmark is invalid (no invariant can verify it),
                      and no invariant was generated.
FAIL {<vc1>;...}    : The generated invariant fails to verify the VCs: vc1, vc2 etc.
                      where each VC is one of {pre, post, trans}.
FAIL (NO SOLUTION)  : The benchmark is invalid (no invariant can verify it),
                      but an invariant (that is not empty/false) was generated.
[TIMEOUT] <verdict> : Invariant inference timed out.
                      With an empty (false) invariant, <verdict> is one of the verdicts above.
```

Try `./loopinvgen.sh -h` for other options that allow more control over the inference process.

</details>


## Testing

Execute `./test_all.sh -b benchmarks/LIA` to run LoopInvGen on all benchmarks in [benchmarks/LIA].

**Note:** Within `test_all.sh`,
we trap <kbd>CTRL</kbd>+<kbd>C</kbd> (`SIGINT` signal) to kill the currently running benchmark,
and <kbd>CTRL</kbd>+<kbd>\\</kbd> (`SIGQUIT` signal) to kill the `test_all.sh` script with its child processes.

<details>

The `test_all.sh` script invokes LoopInvGen for invariant inference,
and then verifies that the generated invariant is sufficient to prove correctness of the SyGuS benchmark.  
For each benchmark, it generates one of the verdicts mentioned [above](#verifying-generated-invariants), or:
```
[SKIPPED] <verdict> : Invariant inference was skipped for an already passing benchmark.
                      <verdict> is one of the PASS verdicts above.
```

#### Caching of Results

Since `test_all.sh` caches results from previous runs, it skips benchmarks that are known to be passing.  
This may be disabled by:
- using the `-r` or `--rerun-cached` switch with `test_all.sh`, or
- deleting the previous log directory (default: `_log`), or
- specifying a new log directory (`-l _new_log`).

#### Benchmarking with Other Inference Tools

`test_all.sh` is a generic benchmarking script that may run any invariant inference tool.
which accepts the SyGuS format. This makes it easier for us to compare various tools easily.  
To use an invariant inference tool other than LoopInvGen, invoke it as:
`test_all.sh -b <path/to/benchmarks> -T <path/to/tool> [-- -tool -specific -options]`

Try `./test_all.sh -h` for more options.

</details>



[flambda]:        https://caml.inria.fr/pub/docs/manual-ocaml/flambda.html
[travis]:         https://travis-ci.org/SaswatPadhi/LoopInvGen
[z3]:             https://github.com/Z3Prover/z3
[benchmarks/LIA]: benchmarks/LIA
[SyGuSCOMP17]:    http://www.sygus.org/SyGuS-COMP2017.html