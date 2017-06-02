open Core
open Types
open VPIE

let abs_job = PIE.create_job
  ~f:(fun [ VInt x ] -> VInt (if x > 0 then x else -x))
  ~args:([ "x", TInt ])
  ~post:(fun inp res ->
           match inp , res with
           | [ VInt x ], Ok (VInt y) -> x = y
           | _ -> false)
  ~features:[ ]
  ~tests:(List.map [(-1) ; 3 ; 0 ; (-2) ; 6] ~f:(fun i -> [VInt i]))

let abs_post_desc = "(or (and (>= x 0) (= x x))
                         (and (< x 0) (= x (- x))))"

let abs_equal_precondition () =
  let z3 = ZProc.create()
  in ignore (ZProc.run_queries ~local:false z3 ~db:[ "(declare-var x Int)" ] [])
  ; let res = learnVPreCond ~z3 (abs_job , abs_post_desc)
    in ZProc.close z3
     ; Alcotest.(check string) "identical" "(>= x 0)" res

let all = [
  "Abs Equal Precondition",   `Quick,   abs_equal_precondition  ;
]