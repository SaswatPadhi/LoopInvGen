open Base

open Expr

let components = let (=/=) = (fun x y -> (not (Expr.equal x y))) in [
  {
    name = "not";
    codomain = Type.BOOL;
    domain = [Type.BOOL];
    is_argument_valid = (function
                         | [FCall (comp, _)] when String.equal comp.name "not"
                           -> false
                         | [Const _] -> false
                         | [_] -> true
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Bool x] -> Value.Bool (not x));
    to_string = (fun [@warning "-8"] [a] -> "(not " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "and";
    codomain = Type.BOOL;
    domain = [Type.BOOL;Type.BOOL];
    is_argument_valid = (function
                         | [(Const _) ; _] | [_ ; (Const _)] -> false
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Bool x ; Value.Bool y] -> Value.Bool (x && y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(and " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "or";
    codomain = Type.BOOL;
    domain = [Type.BOOL;Type.BOOL];
    is_argument_valid = (function
                         | [(Const _) ; _] | [_ ; (Const _)] -> false
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Bool x ; Value.Bool y] -> Value.Bool (x || y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(or " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]