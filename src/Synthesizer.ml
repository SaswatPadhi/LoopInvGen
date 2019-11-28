open Core_kernel

open Exceptions
open Utils

module Config = struct
  type cost_attr = Height | Size

  type t = {
    cost_limit : int ;
    cost_attribute : cost_attr ;
    logic : Logic.t ;
    max_expressiveness_level : int ;
    order : int -> int -> float ;
  }

  let default : t = {
    cost_limit = 32 ;
    cost_attribute = Size ;
    logic = Logic.of_string "LIA" ;
    max_expressiveness_level = 1024 ;
    order = (fun g_cost e_cost -> (Int.to_float e_cost) *. (Float.log (Int.to_float g_cost))) ;
  }
end

type task = {
  arg_names : string list ;
  inputs : Value.t array list ;
  outputs : Value.t array ;
  constants : Value.t list
}

type stats = {
  mutable synth_time_ms : float ;
  mutable enumerated : int ;
  mutable pruned : int ;
} [@@deriving sexp]

type result = {
  expr : Expr.t ;
  string : string ;
  func : Value.t list -> Value.t ;
  constraints : string list ;
  stats : stats
}

let max_size = 25

exception Success of Expr.t

module DList = Doubly_linked

let divide_size applier arity op_level expr_level remaining_size =
  let rec eq_helper arity remaining_size acc =
    if arity = 1 then
      for l = 0 to expr_level do
        applier ((l,remaining_size) :: acc)
      done
    else
      begin
        for l = 0 to expr_level do
          for s = 1 to remaining_size do
            eq_helper (arity - 1) (remaining_size - s) ((l,s) :: acc)
          done
        done
      end
  in let rec neq_helper arity remaining_size acc =
    if arity = 1 then
      if List.exists acc ~f:(fun (l,_) -> l = expr_level) then
        begin
          for l = 0 to expr_level do
            applier ((l,remaining_size) :: acc)
          done
        end
      else
        applier ((expr_level,remaining_size) :: acc)
    else
      begin
        for l = 0 to expr_level do
          for s = 1 to remaining_size do
            neq_helper (arity - 1) (remaining_size - s) ((l,s) :: acc)
          done
        done
      end
  in if expr_level = op_level
     then eq_helper arity remaining_size []
     else neq_helper arity remaining_size []

let divide_height applier arity op_level expr_level remaining_height =
  let rec eq_helper arity remaining_height acc =
    if arity = 1 then
      for l = 0 to expr_level do
        applier ((l,remaining_height) :: acc)
      done
    else
      begin
        for l = 0 to expr_level do
          for s = 0 to remaining_height do
            eq_helper (arity - 1) (remaining_height - s) ((l,s) :: acc)
          done
        done
      end
  in let rec neq_helper arity remaining_height acc =
    if arity = 1 then
      let start_level = if List.for_all acc ~f:(fun (_,s) -> s <= op_level)
                        then 0 else (op_level + 1)
       in for l = start_level to expr_level do
            applier ((l,remaining_height) :: acc)
          done
    else
      begin
        for l = 0 to expr_level do
          for s = 0 to remaining_height do
            neq_helper (arity - 1) (remaining_height - s) ((l,s) :: acc)
          done
        done
      end
  in if expr_level = op_level
     then eq_helper arity remaining_height []
     else neq_helper arity remaining_height []

module Output = struct
  module T = struct
    type t = Value.t array [@@deriving sexp]
    let compare (o1 : t) (o2 : t) : int =
      Array.compare Value.compare o1 o2
  end

  include T
  include Comparable.Make (T)
end

module IntTuple = struct
  module T = struct
    type t = int * int [@@deriving sexp]
    let compare ((i1a, i1b) : t) ((i2a, i2b) : t) : int =
      match Int.compare i1a i2a with
      | 0 -> Int.compare i1b i2b
      | c -> c
  end

  include T
  include Comparable.Make (T)
end

let subtract ~(from : Expr.component list) (comps : Expr.component list) =
  List.filter from ~f:(fun c -> not (List.mem comps c
                                       ~equal:(fun c1 c2 -> String.equal c1.name c2.name)))

let solve_impl (config : Config.t) (task : task) (stats : stats) =
  let typed_components t_type =
    let equal_f cod = Type.(match cod , t_type with
                            | ARRAY _ , ARRAY _ -> true
                            | LIST _ , LIST _ -> true
                            | TVAR _, _ -> true
                            | cod, t_type -> equal cod t_type)
     in Array.(append
          (create ~len:1 [])
          (mapi (init (Base.Int.min config.max_expressiveness_level (length config.logic.components_per_level))
                      ~f:(fun i -> config.logic.components_per_level.(i)))
                ~f:(fun level comps
                    -> List.filter ~f:(fun c -> equal_f c.codomain)
                                   (if level < 1 then comps
                                    else subtract ~from:comps (config.logic.components_per_level.(level - 1))))))
   in

  let int_components = typed_components Type.INT in
  let bool_components = typed_components Type.BOOL in
  let char_components = typed_components Type.CHAR in
  let string_components = typed_components Type.STRING in
  let poly_list_components = typed_components Type.(LIST (TVAR "_")) in
  let poly_array_components = typed_components Type.(ARRAY (TVAR "_", TVAR "_")) in

  let empty_candidates () =
    Array.(init ((length config.logic.components_per_level) + 1)
                ~f:(fun _ -> init config.cost_limit ~f:(fun _ -> DList.create ())))
   in

  let int_candidates = empty_candidates () in
  let bool_candidates = empty_candidates () in
  let char_candidates = empty_candidates () in
  let string_candidates = empty_candidates () in
  let list_candidates = empty_candidates () in
  let array_candidates = empty_candidates () in

  let typed_candidates ?(no_tvar = false) = function
    | Type.INT     -> int_candidates
    | Type.BOOL    -> bool_candidates
    | Type.CHAR    -> char_candidates
    | Type.STRING  -> string_candidates
    | Type.LIST _  -> list_candidates
    | Type.ARRAY _ -> array_candidates
    | Type.TVAR _ when not no_tvar
      -> raise (Internal_Exn "No candidates for TVAR")
    | Type.TVAR _ -> let (@) = Array.append
                      in int_candidates @ bool_candidates @ char_candidates
                       @ string_candidates @ list_candidates @ array_candidates
  in

  let seen_outputs = ref (Set.empty (module Output)) in
  let add_candidate candidates_set level cost (candidate : Expr.synthesized) =
    let old_size = Set.length !seen_outputs
     in seen_outputs := Set.add !seen_outputs candidate.outputs
      ; if (Set.length !seen_outputs) = old_size then false
        else (ignore (DList.insert_last candidates_set.(level).(cost) candidate) ; true)
  in

  let constants = Value.(
    List.dedup_and_sort ~compare
       ( Value.[ Int 0 ; Int 1 ; Bool true ; Bool false ]
       @ (List.map task.constants ~f:(function Int x -> Int (abs x) | x -> x))))
  in
  let add_constant_candidate value =
    let candidate : Expr.synthesized = {
      expr = Expr.Const value;
      outputs = Array.create ~len:(Array.length task.outputs) value;
    } in ignore (add_candidate (typed_candidates (Value.typeof value)) 0 1 candidate)
  in List.(iter (rev constants) ~f:add_constant_candidate)
  ;

  List.iteri task.inputs ~f:(fun i input ->
    ignore (add_candidate (typed_candidates (Value.typeof input.(1))) 0 1
                          { expr = Expr.Var i ; outputs = input }))
  ;

  let f_cost = match config.cost_attribute with Height -> Expr.height | Size -> Expr.size in
  let f_divide = match config.cost_attribute with Height -> divide_height | Size -> divide_size in

  let check (candidate : Expr.synthesized) =
    (* Log.debug (lazy ("  > Now checking (@ cost " ^ (Int.to_string (f_cost candidate.expr)) ^ "): "
                       ^ (Expr.to_string (Array.of_list task.arg_names) candidate.expr))) ; *)
    if Array.equal Value.equal task.outputs candidate.outputs
    then raise (Success candidate.expr)
  in

  let task_codomain = Value.typeof task.outputs.(1)
   in DList.iter ~f:check (typed_candidates task_codomain).(0).(1)
  ;

  let apply_component op_level expr_level cost arg_types applier =
    let rec apply_cells acc arg_types locations =
      match arg_types , locations with
      | typ :: arg_types , (lvl,loc) :: locations
        -> DList.iter ~f:(fun x -> apply_cells (x :: acc) arg_types locations)
                      (typed_candidates ~no_tvar:true typ).(lvl).(loc)
      | ([], []) -> applier (List.rev acc)
      | _ -> raise (Internal_Exn "Impossible case!")
    in f_divide (apply_cells [] arg_types) (List.length arg_types) op_level expr_level (cost - 1)
  in
  let expand_component op_level expr_level cost candidates cand_type (component : Expr.component) =
    let applier (args : Expr.synthesized list) =
      stats.enumerated <- stats.enumerated + 1;
      begin
        Log.debug (lazy ( "Attempting to unify " ^ component.name ^ " : [" ^ (List.to_string_map ~sep:"," ~f:Type.to_string component.domain)
                        ^ "] -> " ^ (Type.to_string component.codomain)));
        Log.debug (lazy ("with [" ^ (List.to_string_map args ~sep:" , "
                                                        ~f:(fun a -> "(" ^ (Expr.to_string (Array.of_list task.arg_names) a.expr)
                                                                   ^ " : " ^ (Type.to_string (Value.typeof a.outputs.(0))) ^ ")")) ^ "]"));
        match Expr.unify_component component (List.map args ~f:(fun a -> Value.typeof a.outputs.(0))) with
        | None -> Log.debug (lazy (" > Unification failure!"))
        | Some unified_component -> begin
            let cod = Type.(match unified_component.codomain with
                            | ARRAY _ -> ARRAY (TVAR "_" , TVAR "_")
                            | LIST _ -> LIST (TVAR "_")
                            | cod -> cod)
             in if not (Type.equal cod cand_type) then
                  Log.debug (lazy ("  > The candidate type " ^ (Type.to_string cand_type) ^
                                   " did not match the codomain " ^ (Type.to_string cod)))
                else begin
                  match Expr.apply unified_component args with
                  | None -> stats.pruned <- stats.pruned + 1
                  | Some result
                    -> let expr_cost = f_cost result.expr
                        in if expr_cost < config.cost_limit
                           then (if Type.equal task_codomain unified_component.codomain then check result)
                         ; if not (add_candidate candidates expr_level expr_cost result)
                           then stats.pruned <- stats.pruned + 1
                  end
            end
          end
    in apply_component op_level expr_level cost component.domain applier
  in
  let ordered_level_cost =
    let grammar_cost level = (List.length constants) * (List.length config.logic.components_per_level.(level-1))
    in List.sort ~compare:(fun (level1,cost1) (level2,cost2)
                           -> Float.compare (config.order (grammar_cost level1) cost1)
                                            (config.order (grammar_cost level2) cost2))
                 (List.cartesian_product (List.range 1 ~stop:`inclusive (Int.min config.max_expressiveness_level (Array.length config.logic.components_per_level)))
                                         (List.range 2 config.cost_limit))
  in
  Log.debug (lazy ( "  $ Exploration order (G,k):" ^ (Log.indented_sep 3)
                  ^ (List.to_string_map ordered_level_cost ~sep:" > "
                       ~f:(fun (l,c) -> "(" ^ (Int.to_string l)
                                      ^ "," ^ (Int.to_string c) ^ ")"))))
  ;

  let seen_level_cost = ref (Set.empty (module IntTuple)) in
  List.iter ordered_level_cost
    ~f:(fun (level,cost)
        -> List.(iter (cartesian_product (range ~stop:`inclusive 1 level) (range 2 cost))
             ~f:(fun (l,c) -> if not (Set.mem !seen_level_cost (l,c))
                              then failwith ( "Internal Error :: Not a well order! "
                                            ^ "Attempted to explore (G=" ^ (Int.to_string level)
                                            ^ ",k=" ^ (Int.to_string cost) ^ ") before (G="
                                            ^ (Int.to_string l) ^ ",k=" ^ (Int.to_string c) ^ ")")))
         ; seen_level_cost := (Set.add !seen_level_cost (level, cost))
         ; List.iter (List.range 1 ~stop:`inclusive level)
             ~f:(fun l -> List.iter2_exn
                            Type.[ (BOOL, bool_candidates)
                                 ; (INT, int_candidates)
                                 ; (CHAR, char_candidates)
                                 ; (STRING, string_candidates)
                                 ; (LIST (TVAR "_"), list_candidates)
                                 ; (ARRAY (TVAR "_", TVAR "_"), array_candidates) ]
                            [ bool_components.(l)
                            ; int_components.(l)
                            ; char_components.(l)
                            ; string_components.(l)
                            ; poly_list_components.(l)
                            ; poly_array_components.(l) ]
                            ~f:(fun (cand_type, cands) comps
                                -> List.iter comps ~f:(expand_component l level cost cands cand_type))))

let solve ?(config = Config.default) (task : task) : result =
  Log.debug (lazy ("Running enumerative synthesis with logic `" ^ (config.logic.name) ^ "`:"));
  let start_time = Time.now () in
  let stats = { enumerated = 0 ; pruned = 0 ; synth_time_ms = 0.0 } in
  try solve_impl config task stats
    ; stats.synth_time_ms <- Time.(Span.(to_ms (diff (now ()) start_time)))
    ; raise NoSuchFunction
  with Success solution
       -> let arg_names_array = Array.of_list task.arg_names in
          let solution_string = Expr.to_string arg_names_array solution in
          let solution_constraints = Expr.get_constraints arg_names_array solution
           in Log.debug (lazy ("  % Enumerated " ^ (Int.to_string stats.enumerated) ^ " expressions ("
                              ^ (Int.to_string stats.pruned) ^ " pruned)"))
            ; Log.debug (lazy ("  % Solution (@ size " ^ (Int.to_string (Expr.size solution))
                              ^ "): " ^ solution_string))
            ; Log.debug (lazy ("  % Constraints: "
                              ^ (if (List.length solution_constraints = 0) then "()"
                                 else String.concat ~sep:" " solution_constraints ^ ")")))
            ; { expr = solution
              ; string = solution_string
              ; func = Expr.to_function solution
              ; constraints = solution_constraints
              ; stats = stats
              }