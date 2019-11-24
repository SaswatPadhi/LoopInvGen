open Base
open Sexp
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
    in Alcotest.(check string) "same" res "(and (<= x 9) (>= x 1))")

let z3_result_to_model_as_array () =
  let result = ["sat"; "true";
  "(model
        (define-fun x () (Array Int Int)
          (_ as-array k!10!12))
        (define-fun y () Int
          10)
          (define-fun k!10!12 ((x!0 Int)) Int
          (ite (= x!0 2) 2
          (ite (= x!0 1) 1
            3))))"]
  in let res = match (z3_result_to_model result) with 
                | Some model -> (
                                  let res_x = match List.Assoc.find model ~equal:String.equal "x" with
                                              | None -> false
                                              | Some value -> (String.equal (Value.to_string value) "(store (store ((as const (Array Int Int)) 3) 2 2) 1 1)")
                                  in let res_y = match List.Assoc.find model ~equal:String.equal "y" with
                                                 | None -> false
                                                 | Some value -> (String.equal (Value.to_string value) "10")
                                  in let res_asarray = match List.Assoc.find model ~equal:String.equal "k!10!12" with
                                                       | None -> true
                                                       | Some value -> false
                                  in res_x && res_y && res_asarray
                                )
                | None -> false
  in Alcotest.(check bool) "identical" true res
    
let all ~(zpath :string) = [
  "Implication_true",     `Quick, (implication_true ~zpath) ;
  "Implication_counter",  `Quick, (implication_counter ~zpath) ;
  "Simplification",       `Quick, (simplification ~zpath) ;
  "Parse as-array format",       `Quick, (z3_result_to_model_as_array) ;
]