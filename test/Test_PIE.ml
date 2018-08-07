open Base
open LoopInvGen
open LoopInvGen.Utils

open PIE

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

let conflicts_to_string cgroup =
  let tests_to_string vs = "[" ^ (List.to_string_map ~sep:"," ~f:Value.to_string vs) ^ "]"
  in "Pos:{"
   ^ List.(to_string_map (sort cgroup.pos ~compare:Poly.compare)
                         ~sep:" ; " ~f:tests_to_string)
   ^ "} + Neg:{"
   ^ List.(to_string_map (sort cgroup.neg ~compare:Poly.compare)
                         ~sep:" ; " ~f:tests_to_string)
   ^ "}"

let abs_conflict_failure () =
  let res = cnf_opt_to_desc (
              learnPreCond abs_job ~conf:{ PIE.default_config with
                                           disable_synth = true })
  in Alcotest.(check string) "identical" "false" res

let abs_conflict_group () =
  let res = List.to_string_map (conflictingTests abs_job)
                               ~sep:"\n" ~f:conflicts_to_string
  in Alcotest.(check string) "identical" "Pos:{[0]} + Neg:{[-2] ; [-1]}" res

let abs_precond_1_cnf () =
  let res = cnf_opt_to_desc (
    learnPreCond (Job.add_feature ~job:abs_job
                    ((fun [@warning "-8"] [Value.Int x] -> x + x = x),
                     "(= x (+ x x))"))
                 ~conf:{ PIE.default_config with
                         disable_synth = true
                       ; for_BFL = { BFL.default_config with
                                     k = 1
                                   ; auto_incr_k = false
                                   }})
  in Alcotest.(check string) "identical" "false" res

let abs_precond_auto_1 () =
  let res = cnf_opt_to_desc (
    learnPreCond (Job.add_feature ~job:abs_job
                    ((fun [@warning "-8"] [Value.Int x] -> x + x = x),
                     "(= x (+ x x))"))
                 ~conf:{ PIE.default_config
                         with disable_synth = true
                            ; for_BFL = { BFL.default_config
                                          with k = 1
                                              ; auto_incr_k = true }})
  in Alcotest.(check string) "identical" "(or (= x (+ x x)) (> x 0))" res

let abs_feature_synthesis () =
  let res = snd (synthFeature ~job:abs_job ~logic:(Logic.of_string "LIA")
                              (List.hd_exn (conflictingTests abs_job)))
  in Alcotest.(check string) "identical" "(= x 0)" res

let abs_zero_initial_features () =
  let res = cnf_opt_to_desc (
    learnPreCond (
      Job.create
      ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (if x > 0 then x else -x))
      ~args:([ "x", Type.INT ])
      ~post:(fun inp res -> match inp , res with
                            | [ Value.Int x ], Ok (Value.Int y) -> x = y
                            | _ -> false)
      (List.map [(-1) ; 3 ; 0 ; (-2) ; 6] ~f:(fun i -> [Value.Int i]))))
  in Alcotest.(check string) "identical" "(<= 0 x)" res

let all = [
  "Abs Conflict Failure",    `Quick, abs_conflict_failure  ;
  "Abs Conflict Group",      `Quick, abs_conflict_group    ;
  "Abs Precond 1-CNF",       `Quick, abs_precond_1_cnf ;
  "Abs Precond Auto >= 1",   `Quick, abs_precond_auto_1 ;
  "Abs Feature Synthesis",   `Quick, abs_feature_synthesis ;
  "Abs No Initial Features", `Quick, abs_zero_initial_features ;
]