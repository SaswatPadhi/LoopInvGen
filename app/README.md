## Example App

This directory shows how to build an app using `LoopInvGen` as an OCaml library.
Our example app, called `App`, resides in the [`App.ml`](App.ml) file.


### Building `App.exe`

The `dune` file within `app` directory specifies the dependencies for our app (called `App`) and some build profiles (optional).
The `dune` file is quite self-explanatory.

To build `App`, you may either:
1. Execute `dune build App.exe` within `LoopInvGen/app` directory, or
2. Execute `dune build app/App.exe` within `LoopInvGen` directory

To run `App`, execute `dune exec app/App.exe` within `LoopInvGen` directory.
It should generate an output similar to the following:

```
PI for { x = abs(x) } with feature learning:
The precondition is: (>= x 0)
  > Total time (ms): 0.30517578125
  > Synth time (ms): [0.]

PI for { append(l1,l2) = [] } without feature learning:
The precondition is: (and (= y []) (= x []))
  > Total time (ms): 0.0152587890625
  > Synth time (ms): []
```
