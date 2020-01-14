open Core_kernel

open SyGuS
open Utils

let setup ?(user_features = []) (s : SyGuS.t) (z3 : ZProc.t) : unit =
  ignore (ZProc.run_queries z3 [] ~scoped:false ~db:((
    ("(set-logic " ^ s.logic ^ ")")
    :: (List.map ~f:var_declaration s.variables))
     @ (List.map ~f:func_definition s.functions)
     @ user_features))

let filter_state ?(trans = true) (model : ZProc.model) : ZProc.model =
  if trans
  then List.filter_map model
                       ~f:(fun (n, v) -> match String.chop_suffix n ~suffix:"!" with
                                         | None -> None
                                         | Some n -> Some (n, v))
  else List.filter model ~f:(fun (n, _) -> not (String.is_suffix n ~suffix:"!"))

let gen_state_from_model (s : SyGuS.t) (m : ZProc.model option)
                         : Value.t list option Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match m with None -> singleton None
  | Some m -> create (fun ~size ~random -> Some (
                List.map s.synth_variables
                         ~f:(fun (v, t) ->
                               match List.Assoc.find m v ~equal:(=)
                               with Some d -> d
                                  | None -> generate (TestGen.for_type t) ~size ~random)))

let transition (s : SyGuS.t) (z3 : ZProc.t) (vals : Value.t list)
               : Value.t list option Quickcheck.Generator.t =
  gen_state_from_model s (
    try begin
      match ZProc.sat_model_for_asserts z3 ~eval_term:s.trans_func.body
              ~db:[ ("(assert " ^ s.trans_func.body ^ ")")
                  ; ( "(assert (and "
                    ^ (Utils.List.to_string_map2 ~sep:" " vals s.synth_variables
                        ~f:(fun d (v, _) -> ("(= " ^ v ^ " " ^
                                            (Value.to_string d) ^ ")")))
                    ^ "))")]
      with None -> None | Some model -> Some (filter_state ~trans:true model)
    end with _ -> None)

let gen_pre_state ?(use_trans = false) (s : SyGuS.t) (z3 : ZProc.t)
                  : Value.t list option Quickcheck.Generator.t =
  Log.info (lazy "Generating an initial state:");
  gen_state_from_model s
    (ZProc.sat_model_for_asserts z3 ~eval_term:s.trans_func.body
          ~db:[ "(assert (and " ^ s.pre_func.body ^ " "
              ^ (if use_trans then s.trans_func.body else "true") ^ "))" ])

let simulate_from (s : SyGuS.t) (z3 : ZProc.t) (head : Value.t list option)
                  : Value.t list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match head with None -> singleton []
  | Some head ->
      let step head ~size ~random =
        let rec step_internal head size =
          Log.info (lazy (" > " ^ (List.to_string_map ~sep:", " ~f:Value.to_string head))) ;
          head :: (match size with
                  | 0 -> []
                  | n -> begin match generate (transition s z3 head) ~size ~random
                               with Some next when next <> head
                                    -> step_internal next (n-1)
                                  | _ -> []
                        end)
        in step_internal head size
      in Log.info (lazy ("New execution (" ^ (List.to_string_map s.synth_variables ~sep:", " ~f:fst) ^ "):"))
       ; create (step head)

let record_states ~size ~seed ~state_chan ~(zpath : string) (s : SyGuS.t) : unit =
  let gen_and_print size z3 : Value.t list option -> int = function
    | None -> 0
    | Some head
      -> let states = Quickcheck.random_value ~size ~seed
                                              (simulate_from s z3 (Some head)) in
         let open Out_channel
          in List.(iter states
                        ~f:(fun s -> output_string state_chan
                                      (to_string_map ~sep:"\t" ~f:Value.to_string s)
                                   ; newline state_chan))
           ; flush state_chan
           ; ignore (ZProc.run_queries
                       z3 ~scoped:false
                       [ "(not (and "
                       ^ (List.to_string_map2
                            s.synth_variables head ~sep:" "
                            ~f:(fun (name, _) value -> ("(= " ^ name ^ " " ^ (Value.to_string value) ^ ")")))
                       ^ "))" ])
           ; (List.length states)
  in ZProc.process ~zpath
       ~random_seed:(Some (string_of_int (Quickcheck.(
                       random_value ~seed (Generator.small_non_negative_int)))))
       (fun z3 -> setup s z3 ;
                  let rec helper avoid size =
                    let open Quickcheck in
                    let sz = size / 2 in
                    let head_1 = random_value ~seed (gen_pre_state s z3) in
                    let added_1 = gen_and_print sz z3 head_1 in
                    let head_2 = random_value ~seed (gen_pre_state ~use_trans:true s z3) in
                    let added_2 = gen_and_print sz z3 head_2
                     in (if added_1 = 0 && added_2 = 0 then ()
                         else let remaining_size = size - (added_1 + added_2)
                               in if remaining_size > 0 then helper avoid remaining_size
                                                        else ())
                   in helper [] size)