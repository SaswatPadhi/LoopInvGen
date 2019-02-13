open Core_kernel

open Exceptions
open Utils

type cost_attr = Height | Size

type config = {
  cost_limit : int ;
  cost_attribute : cost_attr ;
  cost_function : int -> int -> float ;
  logic : Logic.t ;
  max_level : int ;
}

let default_config : config = {
  cost_limit = 25 ;
  cost_attribute = Size ;
  cost_function = (fun g_cost e_cost -> (Int.to_float e_cost) *. (Float.log (Int.to_float g_cost))) ;
  logic = Logic.of_string "LIA" ;
  max_level = 4 ;
}

type task = {
  arg_names : string list ;
  inputs : Value.t array list ;
  outputs : Value.t array
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

let solve_impl consts config task stats=
  let int_components = Array.append
    (Array.create ~len:1 [])
    (Array.mapi (Array.init (Int.min config.max_level (Array.length config.logic.components_per_level))
                            ~f:(fun i -> config.logic.components_per_level.(i)))
                ~f:(fun level comps
                    -> List.filter ~f:(fun c -> Poly.equal c.codomain Type.INT)
                                   (if level < 1 then comps
                                    else subtract ~from:comps (config.logic.components_per_level.(level - 1))))) in
  let bool_components = Array.append
    (Array.create ~len:1 [])
    (Array.mapi (Array.init (Int.min config.max_level (Array.length config.logic.components_per_level))
                            ~f:(fun i -> config.logic.components_per_level.(i)))
                ~f:(fun level comps
                    -> List.filter ~f:(fun c -> Poly.equal c.codomain Type.BOOL)
                                   (if level < 1 then comps
                                    else subtract ~from:comps (config.logic.components_per_level.(level - 1))))) in

  Log.debug (lazy ( "  $ INT Components:"
                  ^ (Array.fold ~init:"" int_components
                       ~f:(fun s l -> s ^ (Log.indented_sep 2) ^ "[" ^ (List.to_string_map l  ~sep:", " ~f:(fun (c : Expr.component) -> c.name)) ^ "]"))))
  ;
  Log.debug (lazy ( "  $ BOOL Components:"
                  ^ (Array.fold ~init:"" bool_components
                       ~f:(fun s l -> s ^ (Log.indented_sep 2) ^ "[" ^ (List.to_string_map l  ~sep:", " ~f:(fun (c : Expr.component) -> c.name)) ^ "]"))))
  ;

  let int_candidates =
    Array.init ((Array.length config.logic.components_per_level) + 1)
      ~f:(fun _ -> Array.init config.cost_limit ~f:(fun _ -> DList.create ())) in
  let bool_candidates =
    Array.init ((Array.length config.logic.components_per_level) + 1)
      ~f:(fun _ -> Array.init config.cost_limit ~f:(fun _ -> DList.create ())) in

  let seen_outputs = ref (Set.empty (module Output)) in
  let add_candidate candidates_set level cost (candidate : Expr.synthesized) =
    let old_size = Set.length !seen_outputs
     in seen_outputs := Set.add !seen_outputs candidate.outputs
      ; if (Set.length !seen_outputs) = old_size then false
        else (ignore (DList.insert_last candidates_set.(level).(cost) candidate) ; true)
  in

  let constants =
    (List.dedup_and_sort ~compare:Value.compare
       ( [ Value.Int 0 ; Value.Int 1 ; Value.Bool true ; Value.Bool false ]
       @ (List.map ~f:(function Value.Int x -> Value.Int (abs x) | x -> x) consts)))
  in
  let add_constant_candidate value =
    let candidate : Expr.synthesized = {
      expr = Expr.Const value;
      outputs = Array.create ~len:(Array.length task.outputs) value;
    } in match Value.typeof value with
         | Type.BOOL -> ignore (add_candidate bool_candidates 0 1 candidate)
         | Type.INT -> ignore (add_candidate int_candidates 0 1 candidate)
  in List.(iter (rev constants) ~f:add_constant_candidate)
  ;

  List.iteri task.inputs ~f:(fun i input ->
    let candidates = match Value.typeof input.(1) with
      | Type.INT -> int_candidates
      | Type.BOOL -> bool_candidates
    in ignore (add_candidate candidates 0 1 { expr = Expr.Var i ; outputs = input }))
  ;

  let f_cost = match config.cost_attribute with Height -> Expr.height | Size -> Expr.size in
  let f_divide = match config.cost_attribute with Height -> divide_height | Size -> divide_size in

  let check (candidate : Expr.synthesized) =
    (* Log.debug (lazy ("  > Now checking (@ cost " ^ (Int.to_string (f_cost candidate.expr)) ^ "): "
                       ^ (Expr.to_string (Array.of_list task.arg_names) candidate.expr))) ; *)
    if Array.equal ~equal:Value.equal task.outputs candidate.outputs
    then raise (Success candidate.expr)
  in

  let task_codomain = Value.typeof task.outputs.(1) in
  begin match task_codomain with
    | Type.INT -> DList.iter ~f:check int_candidates.(0).(1);
    | Type.BOOL -> DList.iter ~f:check bool_candidates.(0).(1);
  end ;

  let apply_component op_level expr_level cost arg_types applier =
    let rec apply_cells acc types locations =
      match types, locations with
      | (typ :: types, (lvl,loc) :: locations)
        -> DList.iter ~f:(fun x -> apply_cells (x :: acc) types locations)
                      begin match typ with
                        | Type.INT -> int_candidates.(lvl).(loc)
                        | Type.BOOL -> bool_candidates.(lvl).(loc)
                      end
      | ([], []) -> applier (List.rev acc)
      | _ -> raise (Internal_Exn "Impossible case!")
    in f_divide (apply_cells [] arg_types) (List.length arg_types) op_level expr_level (cost - 1)
  in
  let expand_component op_level expr_level cost candidates component =
    let applier args =
      stats.enumerated <- stats.enumerated + 1;
      match Expr.apply component args with
      | None -> stats.pruned <- stats.pruned + 1
      | Some result
        -> let expr_cost = f_cost result.expr
            in if expr_cost < config.cost_limit
               then (if Poly.equal task_codomain component.codomain then check result)
             ; if not (add_candidate candidates expr_level expr_cost result)
               then stats.pruned <- stats.pruned + 1
    in apply_component op_level expr_level cost component.domain applier
  in
  let ordered_level_cost =
    let grammar_cost level = (List.length constants) * (List.length config.logic.components_per_level.(level-1))
    in List.sort ~compare:(fun (level1,cost1) (level2,cost2)
                           -> Float.compare (config.cost_function (grammar_cost level1) cost1)
                                            (config.cost_function (grammar_cost level2) cost2))
                 (List.cartesian_product (List.range 1 ~stop:`inclusive (Int.min config.max_level (Array.length config.logic.components_per_level)))
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
                              then failwith ( "Internal Error :: Bad guiding function for synthesis. "
                                            ^ "Exploring (G=" ^ (Int.to_string level)
                                            ^ ",k=" ^ (Int.to_string cost) ^ ") before (G="
                                            ^ (Int.to_string l) ^ ",k=" ^ (Int.to_string c)
                                            ^ ")!")))
         ; seen_level_cost := (Set.add !seen_level_cost (level, cost))
         ; List.iter (List.range 1 ~stop:`inclusive level)
             ~f:(fun l -> List.iter2_exn
                            [bool_candidates ; int_candidates]
                            [bool_components.(l) ; int_components.(l)]
                            ~f:(fun cands comps
                                -> List.iter comps ~f:(expand_component l level cost cands))))

let solve (consts : Value.t list) ~(config : config) (task : task) : result =
  Log.debug (lazy ("Running enumerative synthesis:"));
  let start_time = Time.now () in
  let stats = { enumerated = 0 ; pruned = 0 ; synth_time_ms = 0.0 } in
  try solve_impl consts config task stats
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
