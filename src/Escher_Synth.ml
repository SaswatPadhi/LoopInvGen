open Components
open Escher_Core
open Types

exception Success

type task = {
  target : component ;
  inputs : Vector.t list ;
  components : component list
}

let rec divide f arity target acc =
  if arity = 0 then
    if target = 0 then f acc else ()
  else begin
    for i = 1 to target do
      divide f (arity - 1) (target - i) (i::acc)
    done
  end

(* Rename to "divide" if using the "depth" heuristic, which violates our
   additivity assumption *)
let rec divide_depth f arity target acc =
  if arity = 0 then f acc
  else if arity = 1 && List.for_all (fun x -> x < target) acc
       then f (target::acc)
       else begin
         for i = 0 to target do
           divide f (arity - 1) target (i::acc)
         done
       end

let _unsupported_ = (fun l -> " **UNSUPPORTED** ")

let apply_component (c : component) (args : Vector.t list) =
  if (c.name = "not" && (match (snd (fst (List.hd args)))
                         with Node ("not", _) -> true | _ -> false))
  || (c.name = "*" && (match ((snd (fst List.(hd args))), (snd (fst List.(hd (tl args)))))
                          with (Node _, Node _) -> true
                             | (Node _, Leaf a) -> not (BatString.starts_with a "const_")
                             | (Leaf a, Node _) -> not (BatString.starts_with a "const_")
                             | (Leaf a, Leaf b) -> not (BatString.((starts_with a "const_") || (starts_with b "const_")))))
  then ((("", (fun _ -> VBool false)), Node ("", [])), Array.mapi (fun _ _ -> VError) (snd (List.hd args)))
  else (
    let select i l = List.map (fun x -> x.(i)) l in
    let prs = List.map (fun (((_,x),_),_) -> x) args in
    let values = List.map snd args in
    let new_prog = fun ars -> c.apply (List.map (fun p -> p ars) prs) in
    let new_str = c.dump (List.map (fun (((x,_),_),_) -> x) args) in
    let result = Array.mapi (fun i _ -> c.apply (select i values)) (List.hd values)
    in (((new_str, new_prog), Node (c.name, List.map (fun ((_,x),_) -> x) args)), result))

(* Upper bound on the heuristic value a solution may take *)
let max_h = ref 15

let expand_ = ref "size"
let goal_graph = ref false

let noisy = ref false
let quiet = ref true

let all_solutions = ref []
let synth_candidates = ref 0

let rec is_boring = function
  | (Leaf "0") | (Leaf "[]") -> true
  | (Leaf _) -> false
  | Node (_, args) -> List.for_all is_boring args

let rec fancy = function
  | Leaf _ -> 1
  | Node (x, args) ->
      let h_values = List.map fancy args in
      let h_sum = List.fold_left (+) 0 h_values in
      let size = h_sum in (* estimate size with h_sum *)
      let penalty = 0 in
      let penalty =
        if size <= 3 then penalty
        else if is_boring (Node (x, args)) then 2 + penalty
             else penalty
      in 1 + h_sum + penalty

let hvalue ((_,x),_) =
  match !expand_ with
    | "size" -> program_size x
    | "depth" -> program_height x
    | "fancy" -> fancy x
    | _ -> failwith "Unrecognized expand method!"

type goal_status =
  | Closed of Vector.t
  | Open

and goal = {
  varray : value array;
  mutable status : goal_status; }

let short_goal_string goal = match goal.status with
  | Open -> "<open> " ^ (varray_string goal.varray)
  | Closed v -> "<closed> " ^ (Vector.string v)

let rec print_goal indent goal =
  if String.length indent > 10 then print_endline (indent ^ "...")
  else print_endline (indent ^ "goal: " ^ (varray_string goal.varray))

let solve_impl ?ast:(ast=false) task consts =
  let vector_size = Array.length (snd (List.hd task.inputs)) in
  let components = task.components in

  let final_goal = {
    varray = snd (apply_component task.target task.inputs);
    status = Open; } in

  let goals = ref (VArrayMap.add final_goal.varray final_goal VArrayMap.empty) in

  let close_goal vector goal =
    if !noisy then begin
      print_endline ("Closed goal " ^ (varray_string goal.varray));
      print_endline ("       with " ^ (Vector.string vector));
      end else ();
    goal.status <- Closed vector;
    match final_goal.status with Closed cls -> (all_solutions := cls::all_solutions.contents; if not ast then raise Success else ()) | _ -> ()
  in

  let int_array = Array.make !max_h VSet.empty in
  let bool_array = Array.make !max_h VSet.empty in

  let check_vector v =
    (* Close all matching goals *)
    let (v_closes, _) = partition_map (varray_matches ~typeonly:ast (snd v)) (!goals)
    in if !noisy then begin
         print_endline "--- new vector --------------------------------------";
         print_endline ((string_of_int (hvalue v)) ^ ": " ^ (Vector.string v));
       end else ();
       synth_candidates := 1 + (!synth_candidates);
       List.iter (close_goal v) v_closes; true
  in

  let int_components = List.filter (fun c -> c.codomain = TInt) components in
  let bool_components = List.filter (fun c -> c.codomain = TBool) components in

  let apply_comp f types i =
    let rec apply_cells types acc locations = match types, locations with
      | (typ::typs, i::locs) -> VSet.iter (fun x -> apply_cells typs (x::acc) locs) begin
          match typ with
            | TInt -> int_array.(i)
            | TBool -> bool_array.(i)
          end
      | ([], []) -> f (List.rev acc)
      | _ -> failwith "Impossible!"
    in divide (apply_cells types []) (List.length types) (i-1) []
  in
  let expand_component c array i =
    let f x =
      let vector = apply_component c x in
      let h_value = hvalue vector in
      let has_err = Array.fold_left (fun p x -> match x with VError -> true | _ -> p) false (snd vector) in
      if (h_value < !max_h && (not has_err))
      then ((if not (!noisy) then ()
            else print_endline (string_of_int h_value ^ ">>" ^ (Vector.string vector)));
            array.(h_value) <- VSet.add vector (array.(h_value)))
    in apply_comp f c.domain i
  in
  let expand_type (mat, components) i =
    List.iter (fun c -> expand_component c mat i) components;
  in
  let expand i =
    List.iter (fun x -> expand_type x i)
              [(int_array, int_components);
               (bool_array, bool_components)]
  in
  let zero = ((("0", (fun ars -> VInt 0)), Leaf "0"), Array.make vector_size (VInt 0)) in
  let btrue = ((("true", (fun ars -> VBool true)), Leaf "true"), Array.make vector_size (VBool true)) in
  let bfalse = ((("false", (fun ars -> VBool false)), Leaf "false"), Array.make vector_size (VBool false)) in
  if !quiet then () else (
    print_endline ("Inputs: ");
    List.iter (fun v -> print_endline ("   " ^ (Vector.string v))) task.inputs;
    print_endline ("Goal: " ^ (varray_string final_goal.varray)));
    (*TODO: Only handling string and int constants, extend for others*)
  int_array.(1)
    <- List.fold_left (fun p i -> VSet.add ((((string_of_int i), (fun ars -> VInt i)), Leaf ("const_" ^ (string_of_int i))),
                                            Array.make vector_size (VInt i)) p)
                      (VSet.singleton zero)
                      (BatList.sort_unique compare (1 :: (-1) :: 2 :: 3 :: 5 ::
                                                    (BatList.filter_map (fun v -> match v with
                                                                                  | VInt x -> Some x
                                                                                  | _ -> None) consts)));
  bool_array.(1)   <- VSet. add btrue (VSet.singleton bfalse);
  List.iter (fun input ->
    let array = match (snd input).(1) with
      | VInt _ -> int_array
      | VBool _ -> bool_array
      | VError -> failwith "Error in input"
      | VDontCare -> failwith "Underspecified input"
    in array.(1) <- VSet.add input array.(1))
  task.inputs;
  for i = 2 to !max_h-1; do
    int_array.(i-1) <- VSet.filter check_vector int_array.(i-1);
    bool_array.(i-1) <- VSet.filter check_vector bool_array.(i-1);
    begin match final_goal.status with
      | Closed p -> final_goal.status <- Open
      | Open -> () end;
    (*(if !quiet then prerr_string else print_endline) (" @" ^ (string_of_int i)); flush_all();*)
    if !noisy then begin
      let print_goal k _ = print_endline (" * " ^ (varray_string k)) in
        print_endline ("Goals: ");
        VArrayMap.iter print_goal (!goals);
    end else ();
    expand i;
  done

  let solve ?ast:(ast=false) task consts =
    all_solutions := [] ; synth_candidates := 0;
  (try solve_impl ~ast:ast task consts with Success -> ());
  if not (!quiet) then (print_endline "Synthesis Result: "; List.iter (fun v -> print_endline (Vector.string v)) all_solutions.contents) ;
  List.rev_map (fun (((x,y),_),_) -> (x, y)) all_solutions.contents

  let default_components = Th_Bool.components @ Th_LIA.components