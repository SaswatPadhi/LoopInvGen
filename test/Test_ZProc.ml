open Base
open LoopInvGen
open LoopInvGen.ZProc

let model_to_string (m : model option) : string =
  match m with
  | None -> "false"
  | Some [ var, value ]
    -> "(= " ^ var ^ " " ^ (Value.to_string value) ^ ")"
  | Some var_val_list
    -> "(and" ^ (Utils.List.to_string_map var_val_list ~sep:" "
                   ~f:(fun (var, value) -> "(= " ^ var ^ " "
                                         ^ (Value.to_string value) ^ ")"))
     ^ ")"

let implication_true ~(zpath : string) () =
  process ~zpath (fun z3 ->
    ignore (run_queries ~scoped:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = (model_to_string (implication_counter_example
                                  z3 "(> x 1)" "(> x 0)"))
    in Alcotest.(check string) "same" res "false")

let implication_counter ~(zpath : string) () =
  process ~zpath (fun z3 ->
    ignore (run_queries ~scoped:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = (model_to_string (implication_counter_example
                                  z3 "(> x 1)" "(> x 2)"))
    in Alcotest.(check string) "same" res "(= x 2)")

let simplification ~(zpath : string) () =
  process ~zpath (fun z3 ->
    ignore (run_queries ~scoped:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = simplify z3 "(and (or (>= x 1) (> x 5)) (<= x 9))"
    in Alcotest.(check string) "same" res "(and (>= x 1) (<= x 9))")

let all ~(zpath :string) = [
  "Implication_true",     `Quick, (implication_true ~zpath) ;
  "Implication_counter",  `Quick, (implication_counter ~zpath) ;
  "Simplification",       `Quick, (simplification ~zpath) ;
]