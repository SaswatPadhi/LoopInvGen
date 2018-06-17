(* FIXME: Not maintained; needs updates. *)

open Core
open Exceptions

let implication_true ~(zpath : string) () =
  ZProc.process ~zpath (fun z3 ->
    ignore (ZProc.run_queries ~scoped:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = ZProc.(model_to_string (implication_counter_example
                                        z3 "(> x 1)" "(> x 0)"))
    in Alcotest.(check string) "same" res "false")

let implication_counter ~(zpath : string) () =
  ZProc.process ~zpath (fun z3 ->
    ignore (ZProc.run_queries ~scoped:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = ZProc.(model_to_string (implication_counter_example
                                        z3 "(> x 1)" "(> x 2)"))
    in Alcotest.(check string) "same" res "(= x 2)")

let simplification ~(zpath : string) () =
  ZProc.process ~zpath (fun z3 ->
    ignore (ZProc.run_queries ~scoped:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = ZProc.simplify z3 "(and (or (>= x 1) (> x 5)) (<= x 9))"
    in Alcotest.(check string) "same" res "(and (>= x 1) (<= x 9))")

let all ~(zpath :string) = [
  "Implication_true",     `Quick, (implication_true ~zpath) ;
  "Implication_counter",  `Quick, (implication_counter ~zpath) ;
  "Simplification",       `Quick, (simplification ~zpath) ;
]