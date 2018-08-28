open Base

open Exceptions
open Utils

type task = {
  logic : Logic.t ;
  arg_names : string list ;
  inputs : Value.t array list ;
  outputs : Value.t array
}

type result = {
  expr : Expr.t ;
  string : string ;
  func : Value.t list -> Value.t ;
  constraints : string list
}

let explored = ref 0
let rejected = ref 0

let max_size = 25

exception Success of Expr.t

let rec divide f arity target acc =
  if arity = 0 then
    if target = 0 then f acc else ()
  else begin
    for i = 1 to target do
      divide f (arity - 1) (target - i) (i::acc)
    done
  end

module SynthesizedWithUniqueOutput = struct
  module T = struct
    type t = Expr.synthesized [@@deriving sexp]
    let compare (s1 : t) (s2 : t) : int =
      Array.compare Value.compare s1.outputs s2.outputs
  end

  include T
  include Comparable.Make (T)
end

let solve_impl consts task =
  let int_components = List.filter ~f:(fun c -> Poly.equal c.codomain Type.INT) task.logic.components in
  let bool_components = List.filter ~f:(fun c -> Poly.equal c.codomain Type.BOOL) task.logic.components in

  let int_candidates = Array.create ~len:max_size (Set.empty (module SynthesizedWithUniqueOutput)) in
  let bool_candidates = Array.create ~len:max_size (Set.empty (module SynthesizedWithUniqueOutput)) in

  let constants =
    (List.dedup_and_sort ~compare:Value.compare
       ((List.map ~f:(function Value.Int x -> Value.Int (abs x) | x -> x) consts)
        @ [ Value.Int 0 ; Value.Int 1 ; Value.Bool true ; Value.Bool false ]))
  in

  let add_constant_candidate value =
    let candidate : Expr.synthesized = {
      expr = Expr.Const value;
      outputs = Array.create ~len:(Array.length task.outputs) value;
    } in match Value.typeof value with
         | Type.BOOL -> bool_candidates.(1) <- Set.add bool_candidates.(1) candidate
         | Type.INT -> int_candidates.(1) <- Set.add int_candidates.(1) candidate
  in

  (* Log.debug (lazy ("  + Loaded Constants: [" ^ (List.to_string_map constants ~sep:"; " ~f:Value.to_string) ^ "]")); *)
  List.iter constants ~f:add_constant_candidate;

  List.iteri task.inputs ~f:(fun i input ->
    let candidates = match Value.typeof input.(1) with
      | Type.INT -> int_candidates
      | Type.BOOL -> bool_candidates
    in candidates.(1) <- Set.add candidates.(1) { expr = Expr.Var i ; outputs = input })
  ;

  explored := 0 ;
  rejected := 0 ;

  let check (candidate : Expr.synthesized) =
    (* Log.debug (lazy ("  > Now checking (@ size " ^ (Int.to_string (Expr.size candidate.expr)) ^ "): "
                    ^ (Expr.to_string (Array.of_list task.arg_names) candidate.expr))); *)
    if Array.equal ~equal:Value.equal task.outputs candidate.outputs
    then raise (Success candidate.expr)
  in

  let task_codomain = Value.typeof task.outputs.(1) in

  begin match task_codomain with
  | Type.INT -> Set.iter ~f:check int_candidates.(1);
  | Type.BOOL -> Set.iter ~f:check bool_candidates.(1);
  end ;

  let apply_component size arg_types applier =
    let rec apply_cells acc types locations =
      match types, locations with
      | (typ :: typs , i :: locs)
        -> Set.iter ~f:(fun x -> apply_cells (x :: acc) typs locs)
                    begin match typ with
                      | Type.INT -> int_candidates.(i)
                      | Type.BOOL -> bool_candidates.(i)
                    end
      | ([], []) -> applier (List.rev acc)
      | _ -> raise (Internal_Exn "Impossible case!")
    in divide (apply_cells [] arg_types) (List.length arg_types) (size - 1) []
  in
  let expand_component size candidates component =
    let applier args =
      explored := !explored + 1;
      match Expr.apply component args with
      | None -> rejected := !rejected + 1
      | Some result
        -> let h_value = Expr.size result.expr
            in if h_value < max_size
               then (if Poly.equal task_codomain component.codomain then check result)
                  ; candidates.(h_value) <- Set.add candidates.(h_value) result
    in apply_component size component.domain applier
  in
  let expand_type size candidates components =
    List.iter ~f:(expand_component size candidates) components
  in
  let expand size =
    List.iter2_exn ~f:(expand_type size)
                   [bool_candidates ; int_candidates]
                   [bool_components ; int_components]
  in

  for size = 2 to max_size-1 ; do expand size done

let solve (consts : Value.t list) (task : task) : result =
  Log.debug (lazy ("Running enumerative synthesis:"));
  try solve_impl consts task ; raise NoSuchFunction
  with Success solution
       -> let arg_names_array = Array.of_list task.arg_names
           in let solution_string = Expr.to_string arg_names_array solution
           in let solution_constraints = Expr.get_constraints arg_names_array solution
           in Log.debug (lazy ("  # Explored " ^ (Int.to_string !explored) ^ " expressions ("
                              ^ (Int.to_string !rejected) ^ " rejections)"))
            ; Log.debug (lazy ("  # Solution (@ size " ^ (Int.to_string (Expr.size solution))
                              ^ "): " ^ solution_string))
            ; Log.debug (lazy ("  # Constraints: "
                              ^ (if (List.length solution_constraints = 0) then "()"
                                 else String.concat ~sep:" " solution_constraints ^ ")")))
            ; { expr = solution
              ; string = solution_string
              ; func = Expr.to_function solution
              ; constraints = solution_constraints
              }