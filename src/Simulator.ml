open Core
open Exceptions
open SyGuS
open Types

let setup (s : SyGuS.t) (z3 : ZProc.t) : unit =
  ignore (ZProc.run_queries ~local:false z3 ~db:(
    ("(set-logic " ^ s.logic ^ ")") ::
    (List.map ~f:(fun (v, t) -> ("(declare-var " ^ v ^ " " ^
                                 (string_of_typ t) ^ ")"))
              (s.state_vars @ s.trans_vars))) [])

let filter_state ?(trans = true) (model : (string * Types.value) list)
                 : (string * Types.value) list =
  if trans
  then List.filter_map model
                       ~f:(fun (n, v) -> match String.chop_suffix n "!" with
                                         | None -> None
                                         | Some n -> Some (n, v))
  else List.filter model ~f:(fun (n, _) -> String.is_suffix n ~suffix:"!")

let transition (s : SyGuS.t) (z3 : ZProc.t) (vals : value list)
               : value list option =
  match ZProc.sat_model_for_asserts z3
          ~db:[ ("(assert " ^ s.trans.expr ^ ")")
              ; ( "(assert (and "
                ^ (Utils.List.to_string_map2 ~sep:" " vals s.state_vars
                    ~f:(fun d (v, _) -> ("(= " ^ v ^ " " ^
                                         (serialize_value d) ^ ")")))
                ^ "))")]
  with None -> None
     | Some model
       -> let open List in
          let model = filter_state ~trans:true model
          in Some (map2_exn s.state_vars vals
                            ~f:(fun (var, _) v ->
                                  Option.value (Assoc.find model var ~equal:(=))
                                               ~default: v))

let gen_state_from_model (m : ZProc.model option) (s : SyGuS.t) (z3 : ZProc.t)
                         : value list option Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match m with None -> singleton None
  | Some m
    -> create (fun ~size rnd -> Some (
            List.map s.state_vars
                    ~f:(fun (v, t) ->
                          match List.findi ~f:(fun _ (x, _) -> x = v) m
                          with None -> generate (GenTests.typ_gen t) ~size rnd
                              | Some (_, (_, d)) -> d)))

let gen_pre_state ?(avoid = []) ?(use_trans = false) (s : SyGuS.t)
                  (z3 : ZProc.t) : value list option Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match ZProc.sat_model_for_asserts z3
          ~db:[ "(assert (and " ^ s.pre.expr ^ " "
              ^ (if use_trans then s.trans.expr else "true") ^ " "
              ^ (String.concat avoid ~sep:" ") ^ "))" ]
  with None -> singleton None
     | model -> gen_state_from_model model s z3

let simulate_from (s : SyGuS.t) (z3 : ZProc.t) (head : value list option)
                  : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match head with None -> singleton []
  | Some head ->
      let step head ~size random =
        Log.debug (lazy (" > " ^ (Types.serialize_values head))) ;
        let rec step_internal head size =
          head :: (match size with
                  | 0 -> []
                  | n -> begin match transition s z3 head with
                          | None -> []
                          | Some next -> step_internal next (n-1)
                        end)
        in step_internal head size
      in Log.debug (lazy ("New execution: ")) ; create (step head)

let build_avoid_constraints sygus head =
  Option.value_map head ~default:None
                   ~f:(fun head -> Some (SyGuS.value_assignment_constraint
                                           sygus.state_vars head ~negate:true))

let record_states ?(avoid = []) ~size ~seeds ~state_chan ~head_chan
                  (s : SyGuS.t) ~(zpath : string) : unit =
  let record_and_update avoid head size seed z3 : (string list * int) =
    match head with
    | None -> (avoid, 0)
    | _ -> let states = Quickcheck.random_value ~size ~seed
                                              (simulate_from s z3 head) in
           let Some head = build_avoid_constraints s head in
           let open Core.Out_channel
           in List.iter states
                        ~f:(fun s -> output_string state_chan
                                       (Types.serialize_values s)
                                   ; newline state_chan)
            ; output_string head_chan head ; newline head_chan
            ; flush head_chan ; flush state_chan
            ; ((head :: avoid), (List.length states))
  in ZProc.process ~zpath ~init_options: [
        (* "(set-option :smt.arith.random_initial_value true)" *)
     ] (fun z3 ->
       setup s z3 ;
       List.iter seeds ~f:(fun seed ->
         let rec helper avoid size =
           let open Quickcheck in
           let sz = size / 2 in
           let head_1 = random_value (gen_pre_state ~avoid s z3) ~seed ~size in
           let (avoid, added_1) = record_and_update avoid head_1 sz seed z3 in
           let head_2 = random_value (gen_pre_state ~avoid ~use_trans:true s z3)
                                     ~seed ~size in
           let (avoid, added_2) = record_and_update avoid head_2 sz seed z3
            in (if added_1 = 0 && added_2 = 0 then ()
                else let remaining_size = size - (added_1 + added_2)
                      in if remaining_size > 0 then helper avoid remaining_size
                                               else ())
          in helper avoid size))