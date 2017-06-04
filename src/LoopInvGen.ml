open Core
open SyGuS
open Types
open Utils

let learnStrongerThanPost (sygus : SyGuS.t) ~(states : value list list)
                          ~(z3 : ZProc.t) : PIE.desc =
  Log.debug (lazy ("STAGE 1> Learning initial candidate invariant")) ;
  VPIE.learnVPreCond ~consts:sygus.consts ~z3 (
    (PIE.create_pos_job ()
      ~f: (Simulator.build_function
             sygus.post.expr ~z3 ~arg_names:(List.map sygus.state_vars ~f:fst))
      ~args: sygus.state_vars
      ~post: (fun _ res -> match res with
                           | Ok v when v = vtrue -> true
                           | _ -> false)
      ~pos_tests: states
    ),
    sygus.post.expr
  )

let rec strengthenForInductiveness ~(sygus : SyGuS.t) (inv : PIE.desc)
                                   ~(states : value list list) ~(z3 : ZProc.t)
                                   : PIE.desc =
  Log.debug (lazy ("STAGE 2> Strengthening for inductiveness:\n  " ^ inv)) ;
  if inv = "false" then inv else
  let inv_def =
    "(define-fun invf (" ^
    (List.to_string_map sygus.inv_vars ~sep:" "
                        ~f:(fun (s, t) -> "(" ^ s ^ " " ^
                                          (Types.string_of_typ t) ^ ")")) ^
    ") Bool " ^ inv ^ ")" in
  let invf' = "(invf " ^ (List.to_string_map sygus.inv_vars ~sep:" "
                                             ~f:(fun (s, _) -> s ^ "!")) ^ ")"
  in ZProc.create_local z3 ~db:[ inv_def
                               ; "(assert " ^ sygus.trans.expr ^ ")"
                               ; "(assert " ^ inv ^ ")" ]
   ; let pre_inv =
       VPIE.learnVPreCond ~consts:sygus.consts ~z3 ~simplify:false (
         (PIE.create_pos_job ()
           ~f:(Simulator.build_function invf'
                 ~z3 ~arg_names:(List.map sygus.state_vars ~f:fst))
           ~args: sygus.state_vars
           ~post: (fun _ res -> match res with
                               | Ok v when v = vtrue -> true
                               | _ -> false)
           ~pos_tests: states
         ),
         invf'
       )
     in ZProc.close_local z3
      ; Log.debug (lazy ("Inductive Delta: " ^ pre_inv))
      ; if pre_inv = "true" then inv
        else let inv = ZProc.simplify z3 ("(and " ^ pre_inv ^ " " ^ inv ^ ")")
              in strengthenForInductiveness ~sygus ~states ~z3 inv

let checkIfWeakerThanPre (inv : PIE.desc) ~(sygus : SyGuS.t) ~(z3 : ZProc.t)
                         : ZProc.model option =
  Log.debug (lazy ("STAGE 3> Checking if weaker than precond:\n  " ^ inv)) ;
  ZProc.implication_counter_example z3 sygus.pre.expr inv

let learnInvariant ~(states : value list list) ?(max_restarts = 8)
                   ?(max_steps_on_restart = 128) ?(base_random_seed = "PIE")
                   (sygus : SyGuS.t) : PIE.desc option =
  let rec helper z3 states tries seed =
    let inv = learnStrongerThanPost sygus ~states ~z3
    in let inv = strengthenForInductiveness inv ~sygus ~states ~z3
    in match checkIfWeakerThanPre inv ~sygus ~z3 with
       | None -> Some inv
       | Some model -> if tries < 1 then None else
           let open Quickcheck
           in helper z3 (states @ (random_value
                                     ~size:max_steps_on_restart
                                     ~seed:(`Deterministic seed)
                                     (Simulator.simulate_from sygus z3 model)))
                        (tries - 1)
                        (seed ^ "#")
  in let z3 = ZProc.create () in Simulator.setup sygus z3
   ; let inv = helper z3 states max_restarts base_random_seed
      in ZProc.close z3 ; inv