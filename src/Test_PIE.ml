(* FIXME: Not maintained; needs updates. *)

open BFL
open Core
open Exceptions
open PIE
open Types
open Utils

let abs_job = create_job ()
  ~f:(fun [@warning "-8"] [ VInt x ] -> VInt (if x > 0 then x else -x))
  ~args:([ "x", TInt ])
  ~post:(fun inp res ->
           match inp , res with
           | [ VInt x ], Ok (VInt y) -> x = y
           | _ -> false)
  ~features:[
    ((fun [@warning "-8"] [VInt x] -> x > 0), "(> x 0)")
  ]
  ~tests:(List.map [(-1) ; 3 ; 0 ; (-2) ; 6] ~f:(fun i -> [VInt i]))

let conflicts_to_string cgroup =
  let tests_to_string vs = "[" ^ (serialize_values ~sep:"," vs) ^ "]"
  in "Pos:{"
   ^ (List.to_string_map (List.sort cgroup.pos ~cmp:compare)
                         ~sep:" ; " ~f:tests_to_string)
   ^ "} + Neg:{"
   ^ (List.to_string_map (List.sort cgroup.neg ~cmp:compare)
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
    learnPreCond (add_features ~job:abs_job
                    [ ((fun [@warning "-8"] [VInt x] -> x + x = x), "(= x (+ x x))") ])
                 ~conf:{ PIE.default_config with
                           disable_synth = true ;
                           for_BFL = { BFL.default_config with
                                         k = 1 ; auto_incr_k = false }})
  in Alcotest.(check string) "identical" "false" res

let abs_precond_auto_1 () =
  let res = cnf_opt_to_desc (
    learnPreCond (add_features ~job:abs_job
                    [ ((fun [@warning "-8"] [VInt x] -> x + x = x), "(= x (+ x x))") ])
                 ~conf:{ PIE.default_config with
                           disable_synth = true ;
                           for_BFL = { BFL.default_config with
                                         k = 1 ; auto_incr_k = true }})
  in Alcotest.(check string) "identical" "(or (= x (+ x x)) (> x 0))" res

let abs_feature_synthesis () =
  let res = List.(to_string_map ~sep:" | " ~f:snd
              (synthFeatures ~job:abs_job (hd_exn (conflictingTests abs_job)) Types.LLIA))
  in Alcotest.(check string) "identical" "(= 0 x)" res

let abs_zero_features () =
  let res = cnf_opt_to_desc (
    learnPreCond (
      create_job ()
      ~f:(fun [@warning "-8"] [ VInt x ] -> VInt (if x > 0 then x else -x))
      ~args:([ "x", TInt ])
      ~post:(fun inp res -> match inp , res with
                            | [ VInt x ], Ok (VInt y) -> x = y
                            | _ -> false)
      ~tests:(List.map [(-1) ; 3 ; 0 ; (-2) ; 6] ~f:(fun i -> [VInt i]))))
  in Alcotest.(check string) "identical" "(> x -1)" res

let all = [
  "Abs Conflict Failure",   `Quick,   abs_conflict_failure  ;
  "Abs Conflict Group",     `Quick,   abs_conflict_group    ;
  "Abs Precond 1-CNF",      `Quick,   abs_precond_1_cnf ;
  "Abs Precond Auto >= 1",  `Quick,   abs_precond_auto_1 ;
  "Abs Feature Synthesis",  `Quick,   abs_feature_synthesis ;
  "Abs Zero Features",      `Quick,   abs_zero_features ;
]