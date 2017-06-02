open Core
open Exceptions

let implication_true () =
  let z3 = ZProc.create()
  in ignore (ZProc.run_queries ~local:false z3 ~db:[ "(declare-var x Int)" ] [])
   ; let res = Option.value_map ~default:"None"
                                (ZProc.implication_counter_example
                                  z3 "(> x 1)" "(> x 0)")
                                ~f:ZProc.model_to_string
   in ZProc.close z3
    ; Alcotest.(check string) "same" res "None"

let implication_counter () =
  let z3 = ZProc.create()
  in ignore (ZProc.run_queries ~local:false z3 ~db:[ "(declare-var x Int)" ] [])
   ; let res = Option.value_map ~default:"None"
                                (ZProc.implication_counter_example
                                  z3 "(> x 1)" "(> x 2)")
                                ~f:ZProc.model_to_string
   in ZProc.close z3
    ; Alcotest.(check string) "same" res "x: 2"

let simplification () =
  let z3 = ZProc.create()
  in ignore (ZProc.run_queries ~local:false z3 ~db:[ "(declare-var x Int)" ] [])
   ; let res = ZProc.simplify z3 "(and (or (>= x 1) (> x 5)) (<= x 9))"
   in ZProc.close z3
    ; Alcotest.(check string) "same" res "(and (>= x 1) (<= x 9))"

let all = [
  "Implication_true",     `Quick, implication_true ;
  "Implication_counter",  `Quick, implication_counter ;
  "Simplification",       `Quick, simplification ;
]