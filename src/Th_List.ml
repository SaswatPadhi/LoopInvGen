open Base

open Expr

let vempty = Value.List ([], Type.TVAR "x")

let components = [
  {
    name = "list-len";
    codomain = Type.INT;
    domain = [Type.LIST (Type.TVAR "t")];
    is_argument_valid = (function | [Const (Value.List _)] -> false | _ -> true) ; 
    evaluate = (function [@warning "-8"] [Value.List (x, _)] -> Value.Int (List.length x));
    to_string = (fun [@warning "-8"] [a] -> "(len " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "list-empty?";
    codomain = Type.BOOL;
    domain = [Type.LIST (Type.TVAR "t")];
    is_argument_valid = (function | [Const (Value.List _)] -> false | _ -> true) ; 
    evaluate = (function [@warning "-8"] [Value.List (x,_)] -> Value.Bool (List.length x = 0));
    to_string = (fun [@warning "-8"] [a] -> "(" ^ a ^ " = [])");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "list-rev";
    codomain = Type.LIST (Type.TVAR "t");
    domain = [Type.LIST (Type.TVAR "t")];
    is_argument_valid = (function | [Const (Value.List _)] -> false | _ -> true) ; 
    evaluate = (function [@warning "-8"] [Value.List (x,t)] -> Value.List (List.rev x, t));
    to_string = (fun [@warning "-8"] [a] -> "(rev " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "list-cons";
    codomain = Type.LIST (Type.TVAR "t");
    domain = [Type.TVAR "t"; Type.LIST (Type.TVAR "t")];
    is_argument_valid = (function | _ -> true);
    evaluate = (function [@warning "-8"] [x; Value.List (xs,t)] -> Value.List (x::xs, t));
    to_string = (fun [@warning "-8"] [a; b] -> "(" ^ a ^ " :: " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "list-hd";
    codomain = Type.TVAR "t";
    domain = [Type.LIST (Type.TVAR "t")];
    is_argument_valid = (function | _ -> true);
    evaluate = (function [@warning "-8"] [Value.List (x::_, _)] -> x);
    to_string = (fun [@warning "-8"] [a] -> "(hd " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "list-tl";
    codomain = Type.TVAR "t";
    domain = [Type.LIST (Type.TVAR "t")];
    is_argument_valid = (function | _ -> true);
    evaluate = (function [@warning "-8"] [Value.List (_::xs, t)] -> Value.List (xs, t));
    to_string = (fun [@warning "-8"] [a] -> "(tl " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "list-eq";
    codomain = Type.BOOL;
    domain = [Type.LIST (Type.TVAR "t"); Type.LIST (Type.TVAR "t")];
    is_argument_valid = (function | _ -> true);
    evaluate = (function [@warning "-8"] 
      [Value.List (a, _); Value.List (b, _)] -> Value.Bool (List.equal ~equal:Value.equal a b));
    to_string = (fun [@warning "-8"] [a; b] -> "(eq " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

(* We use Th_List with only Th_LIA for now. *)
(* let all_components = Th_LIA.components @ components

let () = Stdio.print_endline "Initialization of Meta-components Begins"
let forall_components = List.filter_map ~f:Th_Quant.meta_transform all_components
let () = Stdio.print_endline "Initialization Done"

let all_components = all_components @ Th_Quant.all_components @ forall_components *)