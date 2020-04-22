LoopInvGen
<a href="https://microbadger.com/images/padhi/loopinvgen"><img align="right" src="https://img.shields.io/microbadger/image-size/padhi/loopinvgen.svg?style=flat&label=docker"></img></a>
==========

[![](https://img.shields.io/travis/SaswatPadhi/LoopInvGen/master.svg?logo=travis&style=popout&label=Travis+Build)][travis]
&nbsp;
[![](https://img.shields.io/docker/cloud/build/padhi/loopinvgen.svg?logo=docker&style=popout&label=Docker+Image)][docker-hub]

A data-driven tool that generates provably sufficient loop invariants for program verification.

<p align="center">
  <img src="docs/architecture.png" width="400"/>
  <br>
  <sub>
    [&thinsp;LoopInvGen extends our old (now deactivated) project, PIE -- the Precondition Inference Engine.&thinsp;]
  </sub>
</p>


---

[**Installation**](#installation)
&nbsp; &nbsp; &vert; &nbsp; &nbsp;
[Invariant Inference](#invariant-inference)
&nbsp;&middot;&nbsp;
[Batch Verification](#batch-verification)
&nbsp; &nbsp; &vert; &nbsp; &nbsp;
[_Use as a Library_](app/)
&nbsp; &nbsp; &vert; &nbsp; &nbsp;
[Citing LoopInvGen](#citing-loopinvgen)
&nbsp;&middot;&nbsp;
[License (MIT)](LICENSE.md)

---

#### :page_with_curl: Papers and Presentations

- [CAV 2019](http://i-cav.org/2019) --
  Paper on the [_Hybrid Enumeration_ (HEnum)](https://saswatpadhi.github.io/assets/pdf/cav2019_overfitting.pdf) technique used for "feature" synthesis within LoopInvGen
- [PLDI 2016](http://conf.researchr.org/home/pldi-2016) --
  Original paper on the [_Precondition Inference Engine_ (PIE)](https://saswatpadhi.github.io/assets/pdf/pldi2016_pie.pdf), the backbone of LoopInvGen
  <br><br>
- [SyGuS-Comp 2019] (in conjunction with CAV and SYNT 2019) --
  Solver [Presentation](docs/2019_SyGuS-Comp-Presentation.pdf) and [Description](docs/2019_SyGuS-Comp-Description.pdf)
- [SyGuS-Comp 2018] (a satellite event of CAV and SYNT at FLoC 2018) --
  Solver [Presentation](docs/2018_SyGuS-Comp-Presentation.pdf) and [Description](docs/2018_SyGuS-Comp-Description.pdf)
- [SyGuS-Comp 2017] (in conjunction with CAV and SYNT 2017) --
  Solver [Presentation](docs/2017_SyGuS-Comp-Presentation.pdf) and [Description](docs/2017_SyGuS-Comp-Description.pdf)

#### :trophy: Awards and Honors

- [SyGuS-Comp 2018] -- Inv Track **Winner** ([Results](https://sygus.org/comp/2018/results-slides.pdf) and [Report](https://sygus.org/comp/2018/report.pdf))
- [SyGuS-Comp 2017] -- Inv Track **Winner** ([Results](https://sygus.org/comp/2017/results-slides.pdf) and [Report](https://sygus.org/comp/2017/report.pdf))

## Installation

### Using `docker` (recommended)

_**Note:** The docker image may consume  ~&hairsp;3&hairsp;GB of disk space._

We recommend running LoopInvGen within a docker container,
since they have negligible performance overhead.
(See [this report](http://domino.research.ibm.com/library/cyberdig.nsf/papers/0929052195DD819C85257D2300681E7B/$File/rc25482.pdf))

0. [Get `docker` for your OS](https://docs.docker.com/install).
1. Pull our docker image<sup>[#](#note_1)</sup>: `docker pull padhi/loopinvgen`.
2. Run a container over the image: `docker run -it padhi/loopinvgen`.<br>
   This would give you a `bash` shell within LoopInvGen directory.

<a name="note_1"><sup>#</sup></a> Alternatively, you could also build the Docker image locally:

```bash
docker build -t padhi/loopinvgen github.com/SaswatPadhi/LoopInvGen
```

Docker containers are isolated from the host system.
Therefore, to run LoopInvGen on SyGuS files residing on the host system,
you must first [bind mount] them while running the container:

```bash
docker run -v /host/dir:/home/opam/LoopInvGen/shared -it padhi/loopinvgen
```

The `/host/dir` on the host system would then be accessible within the container at `~/LoopInvGen/shared` (with read+write permissions).

<details>

<summary> Docker also allows you to easily limit the container's memory and/or CPU usage.</summary>

```bash
# Create a LoopInvGen container with 4GB memory, no swap and 1 CPU
$ docker run -it --memory=4g --memory-swap=4g --cpus=1 padhi/loopinvgen
```

See [the official Docker guide](https://docs.docker.com/config/containers/resource_constraints)
for more details on applying resource constraints.

</details>


### Manual Installation

<details>

<summary><kbd>CLICK</kbd> to reveal instructions</summary>

#### 0. Get the required packages for your OS.

Please see the [`Dockerfile`](Dockerfile#L19-L21) for the complete list of required packages
for building LoopInvGen and its dependencies.  
Most of these packages are already installed on standard installations of most *nix distributions,
except, may be, these: `aspcud libgmp-dev libomp-dev m4`.

#### 1. Install `opam` package manager for OCaml.

See <https://opam.ocaml.org/doc/Install.html> for detailed instructions.

#### 2. Install `ocaml` >= 4.08.0.
We recommend using an OCaml compiler with [`flambda`][flambda] optimizations enabled.
For example, with [opam](https://opam.ocaml.org/) 2.0+, you could run `opam switch create 4.10.0+flambda`.

#### 3. `opam install` the dependencies.
```bash
$ opam install alcotest.1.1.0 core.v0.13.0 dune.2.5.1
```

#### 4. Get the [Z3 project][z3].
We have tested LoopInvGen with the latest stable version of Z3 (4.8.7).
You could either:
- `git checkout https://github.com/Z3Prover/z3.git` for the bleeding-edge version, or
- `wget https://github.com/Z3Prover/z3/archive/z3-4.8.7.zip && unzip z3-4.8.7.zip` for the stable version

#### 5. `git clone` this project, and build everything.
```bash
$ ./scripts/build_all.sh -z /PATH/TO/z3_dir
```
The `build_all.sh` script would build Z3, copy it to `_dep/`, and then build LoopInvGen.
Alternatively, you can copy a precompiled version of Z3 to a `_dep` directory at the root of the repository,
and simply run `./scripts/build_all.sh`.

For debug builds, use the `-D` or `--debug` switch when invoking `build_all.sh`.

For future builds after any changes to the source code, you only need to run `dune build`.
You can configure the build profile to either `debug` or `optimize` (default),
using: `dune build --profile <profile>`.  

</details>

## Invariant Inference

Infer invariants for SyGuS-INV benchmarks by invoking LoopInvGen as:
```bash
$ ./loopinvgen.sh benchmarks/LIA/2016.SyGuS-Comp/array.sl
(define-fun inv-f ((x Int) (y Int) (z Int)) Bool (not (and (>= x 5) (not (<= y z)))))
```

**Note:** LoopInvGen processes benchmarks in multiple stages.
We trap <kbd>CTRL</kbd>+<kbd>C</kbd> (`SIGINT` signal) to break out of the current stage,
and <kbd>CTRL</kbd>+<kbd>\\</kbd> (`SIGQUIT` signal) to kill LoopInvGen and with its child processes.

#### Inference Timeout

You may use the `-t` flag to run LoopInvGen with a maximum limit
on the number of _seconds_ (wall-clock time) for which the inference algorithm may run.
```bash
$ ./loopinvgen.sh -t 8 benchmarks/LIA/2016.SyGuS-Comp/array.sl
```

For timeout based on CPU time, you may use [`ulimit`](https://ss64.com/bash/ulimit.html).

#### Manually Adding Features

You may use the `-F` flag to preseed LoopInvGen's inference engine
with custom features (written in SMTLib format).
```bash
$ ./loopinvgen.sh -F benchmarks/NIA/2018.CHI_InvGame/~features/s10.some.smt2.input benchmarks/NIA/2018.CHI_InvGame/s10.desugared.sl
```

<details>

<summary><kbd>CLICK</kbd> for further details</summary>

#### Verifying Generated Invariants

The `-v` switch makes LoopInvGen verify the benchmark with the generated invariant:
```bash
$ ./loopinvgen.sh -v benchmarks/LIA/2016.SyGuS-Comp/array.sl
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


## Batch Verification

Execute `./scripts/test_all.sh -b benchmarks/LIA` to run LoopInvGen on all benchmarks in [benchmarks/LIA].
The `test_all.sh` script invokes LoopInvGen for invariant inference,
and then verifies that the generated invariant is sufficient to prove correctness of the SyGuS benchmark.

**Note:** Within `test_all.sh`,
we trap <kbd>CTRL</kbd>+<kbd>C</kbd> (`SIGINT` signal) to kill the currently running benchmark,
and <kbd>CTRL</kbd>+<kbd>\\</kbd> (`SIGQUIT` signal) to kill the `test_all.sh` script with its child processes.

<details>

<summary><kbd>CLICK</kbd> for further details</summary>

For each benchmark, the `test_all.sh` script generates one of the verdicts mentioned [above](#verifying-generated-invariants), or:
```
[SKIPPED] <verdict> : Invariant inference was skipped for an already passing benchmark.
                      <verdict> is one of the PASS verdicts above.
```

#### Rerunning Failed Benchmarks

The `test_all.sh` script creates a new log directory and tests all benchmarks each time it is run.
However, one may want to rerun only the previously failed benchmarks, for example with a different timeout,
from a previously failing run.
This can be achieved by forcing `test_all.sh` to use a previous log directory, using `-l <old_log_dir>`.

#### Benchmarking with Other Inference Tools

`test_all.sh` is a generic benchmarking script that may run any invariant inference tool
which accepts the SyGuS format. This makes it easier for us to compare various tools easily.  
To use an invariant inference tool other than LoopInvGen, invoke it as:
```bash
$ ./scripts/test_all.sh -b <path/to/benchmarks> -T <path/to/tool> [-- [-tool] [-specific] [-options]]
```

#### Limiting Execution Time

Just like `loopinvgen.sh`, the `test_all.sh` script allows users to limit the
execution time for the invariant inference tools using the `-t` flag.
```bash
$ ./scripts/test_all.sh -b benchmarks/LIA -t 10
```

Try `./scripts/test_all.sh -h` for more options.

</details>

## Citing LoopInvGen

```
@inproceedings{pldi/2016/PadhiSM,
  author    = {Saswat Padhi and Rahul Sharma and Todd D. Millstein},
  title     = {Data-Driven Precondition Inference with Learned Features},
  booktitle = {Proceedings of the 37th {ACM} {SIGPLAN} Conference on Programming
               Language Design and Implementation, {PLDI} 2016, Santa Barbara, CA,
               USA, June 13-17, 2016},
  pages     = {42--56},
  year      = {2016},
  url       = {http://doi.acm.org/10.1145/2908080.2908099},
  doi       = {10.1145/2908080.2908099}
}
```

[benchmarks/LIA]:     benchmarks/LIA

[flambda]:            https://caml.inria.fr/pub/docs/manual-ocaml/flambda.html
[bind mount]:         https://docs.docker.com/storage/bind-mounts

[SyGuS-Comp 2017]:    https://sygus.org/comp/2017
[SyGuS-Comp 2018]:    https://sygus.org/comp/2018
[SyGuS-Comp 2019]:    https://sygus.org/comp/2019

[docker-hub]:         https://hub.docker.com/r/padhi/loopinvgen
[travis]:             https://travis-ci.org/SaswatPadhi/LoopInvGen
[z3]:                 https://github.com/Z3Prover/z3