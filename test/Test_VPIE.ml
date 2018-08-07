open Base
open LoopInvGen

let abs_job = Job.create
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (if x > 0 then x else -x))
  ~args:([ "x", Type.INT ])
  ~post:(fun inp res ->
           match inp , res with
           | [ Value.Int x ], Ok (Value.Int y) -> x = y
           | _ -> false)
  (List.map [(-1) ; 3 ; 0 ; (-2) ; 6] ~f:(fun i -> [Value.Int i]))

let abs_post_desc = "(or (and (>= x 0) (= x x))
                         (and (< x 0) (= x (- x))))"

let abs_equal_precondition ~(zpath : string) () =
  ZProc.(process ~zpath (fun z3 ->
    ignore (run_queries ~scoped:false z3 ~db:[ "(declare-var x Int)" ] []);
    let res = VPIE.learnVPreCond ~z3 ~post_desc:abs_post_desc abs_job in
    let counter = equivalence_counter_example z3 res "(>= x 0)"
    in Alcotest.(check string) "identical" "false" (Test_ZProc.model_to_string counter)))

let all ~(zpath : string) = [
  "Abs Equal Precondition",   `Quick,   (abs_equal_precondition ~zpath) ;
]