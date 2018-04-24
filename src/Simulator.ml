open Core
open Exceptions
open SyGuS
open Types

let setup (s : SyGuS.t) (z3 : ZProc.t) : unit =
  ignore (ZProc.run_queries ~scoped:false z3 ~db:(
    ("(set-logic " ^ s.logic ^ ")") ::
    (List.map ~f:(fun (v, t) -> ("(declare-var " ^ v ^ " " ^
                                 (string_of_typ t) ^ ")"))
              (s.state_vars @ s.trans_vars))) [])

let filter_state ?(trans = true) (model : ZProc.model) : ZProc.model =
  if trans
  then List.filter_map model
                       ~f:(fun (n, v) -> match String.chop_suffix n "!" with
                                         | None -> None
                                         | Some n -> Some (n, v))
  else List.filter model ~f:(fun (n, _) -> not (String.is_suffix n ~suffix:"!"))

let gen_state_from_model (s : SyGuS.t) (z3 : ZProc.t) (m : ZProc.model option)
                         : value list option Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match m with None -> singleton None
  | Some m
    -> create (fun ~size rnd -> Some (
            List.map s.state_vars
                    ~f:(fun (v, t) ->
                          match List.Assoc.find m v ~equal:(=)
                          with None -> generate (GenTests.typ_gen t) ~size rnd
                             | Some d -> d)))

let transition (s : SyGuS.t) (z3 : ZProc.t) (vals : value list)
               : value list option Quickcheck.Generator.t =
  gen_state_from_model s z3 (
    try begin
      match ZProc.sat_model_for_asserts z3
              ~db:[ ("(assert " ^ s.trans.expr ^ ")")
                  ; ( "(assert (and "
                    ^ (Utils.List.to_string_map2 ~sep:" " vals s.state_vars
                        ~f:(fun d (v, _) -> ("(= " ^ v ^ " " ^
                                            (serialize_value d) ^ ")")))
                    ^ "))")]
      with None -> None | Some model -> Some (filter_state ~trans:true model)
    end with _ -> None)

let gen_pre_state ?(avoid = []) ?(use_trans = false) (s : SyGuS.t)
                  (z3 : ZProc.t) : value list option Quickcheck.Generator.t =
  gen_state_from_model s z3
    (ZProc.sat_model_for_asserts z3
          ~db:[ "(assert (and " ^ s.pre.expr ^ " "
              ^ (if use_trans then s.trans.expr else "true") ^ " "
              ^ (String.concat avoid ~sep:" ") ^ "))" ])

let simulate_from (s : SyGuS.t) (z3 : ZProc.t) (head : value list option)
                  : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match head with None -> singleton []
  | Some head ->
      let step head ~size rnd =
        Log.debug (lazy (" > " ^ (Types.serialize_values head))) ;
        let rec step_internal head size =
          head :: (match size with
                  | 0 -> []
                  | n -> begin match generate (transition s z3 head) ~size rnd
                               with Some next when next <> head
                                    -> step_internal next (n-1)
                                  | _ -> []
                        end)
        in step_internal head size
      in Log.debug (lazy ("New execution: ")) ; create (step head)

let build_avoid_constraints sygus head =
  Option.value_map head ~default:None
                   ~f:(fun head -> Some (SyGuS.value_assignment_constraint
                                           sygus.state_vars head ~negate:true))

let record_states ?(avoid = []) ?(z3_randomness = false) ~size ~seed
                  ~state_chan ~(zpath : string) (s : SyGuS.t) : unit =
  let record_and_update avoid head size z3 : (string list * int) =
    match head with
    | None -> (avoid, 0)
    | _ -> let states = Quickcheck.random_value ~size ~seed
                                                (simulate_from s z3 head) in
           let [@warning "-8"] Some head = build_avoid_constraints s head in
           let open Core.Out_channel
           in List.iter states
                        ~f:(fun s -> output_string state_chan
                                       (Types.serialize_values s)
                                   ; newline state_chan)
            ; flush state_chan
            ; ((head :: avoid), (List.length states))
  in ZProc.process ~zpath
       ~random_seed:(Some (string_of_int (Quickcheck.(
                       random_value ~seed (Generator.small_non_negative_int)))))
       (fun z3 -> setup s z3 ;
          let rec helper avoid size =
            let open Quickcheck in
            let sz = size / 2 in
            let head_1 = random_value (gen_pre_state ~avoid s z3) ~seed in
            let (avoid, added_1) = record_and_update avoid head_1 sz z3 in
            let head_2 = random_value (gen_pre_state ~avoid ~use_trans:true s z3)
                                      ~seed in
            let (avoid, added_2) = record_and_update avoid head_2 sz z3
            in (if added_1 = 0 && added_2 = 0 then ()
                else let remaining_size = size - (added_1 + added_2)
                      in if remaining_size > 0 then helper avoid remaining_size
                                               else ())
          in helper avoid size)