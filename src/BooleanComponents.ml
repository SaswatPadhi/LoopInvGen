open Base

open Expr

let all = [
  {
    name = "not";
    codomain = Type.BOOL;
    domain = [Type.BOOL];
    is_argument_valid = (function
                         | [FCall (comp, _)] when String.equal comp.name "not"
                           -> false
                         | [ e ] -> not (is_constant e)
                         | _ -> false);
    evaluate = (fun [@warning "-8"] [Value.Bool x] -> Value.Bool (not x));
    to_string = (fun [@warning "-8"] [a] -> "(not " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "and";
    codomain = Type.BOOL;
    domain = [Type.BOOL; Type.BOOL];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x || is_constant y))
                         | _ -> false);
    evaluate = (fun [@warning "-8"] [Value.Bool x ; Value.Bool y] -> Value.Bool (x && y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(and " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "or";
    codomain = Type.BOOL;
    domain = [Type.BOOL; Type.BOOL];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x || is_constant y))
                         | _ -> false);
    evaluate = (fun [@warning "-8"] [Value.Bool x ; Value.Bool y] -> Value.Bool (x || y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(or " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let levels = [| all |]