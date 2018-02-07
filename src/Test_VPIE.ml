open Core
open Types
open VPIE

let abs_job = PIE.create_job ()
  ~f:(fun [@warning "-8"] [ VInt x ] -> VInt (if x > 0 then x else -x))
  ~args:([ "x", TInt ])
  ~post:(fun inp res ->
           match inp , res with
           | [ VInt x ], Ok (VInt y) -> x = y
           | _ -> false)
  ~tests:(List.map [(-1) ; 3 ; 0 ; (-2) ; 6] ~f:(fun i -> [VInt i]))

let abs_post_desc = "(or (and (>= x 0) (= x x))
                         (and (< x 0) (= x (- x))))"

let abs_equal_precondition ~(zpath : string) () =
  ZProc.(process ~zpath (fun z3 ->
    ignore (run_queries ~scoped:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = learnVPreCond ~z3 (abs_job , abs_post_desc) in
    let counter = equivalence_counter_example z3 res "(>= x 0)"
    in Alcotest.(check string) "identical" "false" (model_to_string counter)))

let all ~(zpath : string) = [
  "Abs Equal Precondition",   `Quick,   (abs_equal_precondition ~zpath) ;
]