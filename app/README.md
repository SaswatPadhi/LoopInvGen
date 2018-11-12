## Example App

This directory shows how to build an app (our example app is called `App`),
using `LoopInvGen` as an OCaml library.

The dummy source file ([`App.ml`](App.ml)),
simply infers a precondition to ensure that the absolute value function returns its argument value.

### Building `App.exe`

The `dune` file within `app` directory specifies the dependencies for our app (called `App`) and some build profiles (optional).
The `dune` file is quite self-explanatory.

To build `App`, you may either:
1. Execute `dune build App.exe` within `LoopInvGen/app` directory, or
2. Execute `dune build app/App.exe` within `LoopInvGen` directory

To run `App`, execute `dune exec app/App.exe` within `LoopInvGen` directory.
It should generate the following output:
```
The precondition is: (<= 0 x)
```