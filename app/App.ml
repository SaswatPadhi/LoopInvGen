open Base
open LoopInvGen

(* a job for inferring a precondition to ensure that the absolute value
   function has a result equal to its argument *)
let abs_job = Job.create
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (if x > 0 then x else -x))
  ~args:([ "x", Type.INT ])
  ~post:(fun inp res ->
           match inp , res with
           | [ Value.Int x ], Ok (Value.Int y) -> x = y
           | _ -> false)
  ~features:[
    ((fun [@warning "-8"] [Value.Int x] -> x > 0), "(> x 0)")
  ]
(List.map [(-1) ; 3 ; 0 ; (-2) ; 6] ~f:(fun i -> [Value.Int i]))                

let () =
  Stdio.print_endline (
      "The precondition is: "
    ^ PIE.cnf_opt_to_desc (PIE.learnPreCond abs_job)
  )
