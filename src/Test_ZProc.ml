open Core
open Exceptions

let implication_true () =
  ZProc.process (fun z3 ->
    ignore (ZProc.run_queries ~local:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = ZProc.(model_to_string (implication_counter_example
                                        z3 "(> x 1)" "(> x 0)"))
    in Alcotest.(check string) "same" res "")

let implication_counter () =
  ZProc.process (fun z3 ->
    ignore (ZProc.run_queries ~local:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = ZProc.(model_to_string (implication_counter_example
                                        z3 "(> x 1)" "(> x 2)"))
    in Alcotest.(check string) "same" res "x: 2")

let simplification () =
  ZProc.process (fun z3 ->
    ignore (ZProc.run_queries ~local:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = ZProc.simplify z3 "(and (or (>= x 1) (> x 5)) (<= x 9))"
    in Alcotest.(check string) "same" res "(and (>= x 1) (<= x 9))")

let all = [
  "Implication_true",     `Quick, implication_true ;
  "Implication_counter",  `Quick, implication_counter ;
  "Simplification",       `Quick, simplification ;
]