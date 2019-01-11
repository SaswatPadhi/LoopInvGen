open Base

open Expr

let is_constant expr =
  let rec helper = function
    | Const _ -> ()
    | Var _ -> raise Caml.Exit
    | FCall (_, exprs) -> List.iter ~f:helper exprs
  in try helper expr ; true
     with Caml.Exit -> false

let components = let (=/=) = (fun x y -> (not (Expr.equal x y))) in [
  {
    name = "int-add";
    codomain = Type.INT;
    domain = [Type.INT; Type.INT];
    is_argument_valid = (function
                         | [x ; FCall (comp, [_ ; y])] when String.equal comp.name "int-sub"
                           -> x =/= y && (x =/= Const (Value.Int 0))
                         | [FCall (comp, [_ ; x]) ; y] when String.equal comp.name "int-sub"
                           -> x =/= y && (y =/= Const (Value.Int 0))
                         | [x ; y] -> (x =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 0))
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Int (x + y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(+ " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-sub";
    codomain = Type.INT;
    domain = [Type.INT; Type.INT];
    is_argument_valid = (function
                         | [(FCall (comp, [x ; y])) ; z] when String.equal comp.name "int-add"
                           -> x =/= z && y =/= z && (z =/= Const (Value.Int 0))
                         | [(FCall (comp, [x ; _])) ; y] when String.equal comp.name "int-sub"
                           -> x =/= y && (y =/= Const (Value.Int 0))
                         | [x ; (FCall (comp, [y ; _]))] when (String.equal comp.name "int-sub"
                                                              || String.equal comp.name "int-add")
                           -> x =/= y
                         | [x ; y] -> (x =/= y)
                                   && (x =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 0))
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Int (x - y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(- " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "lin-int-mult";
    codomain = Type.INT;
    domain = [Type.INT; Type.INT];
    is_argument_valid = (function
                         | [x ; y]
                           -> (x =/= Const (Value.Int 0)) && (x =/= Const (Value.Int 1))
                           && (y =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 1))
                           && (is_constant x || is_constant y)
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Int (x * y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(* " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-leq";
    codomain = Type.BOOL;
    domain = [Type.INT;Type.INT];
    is_argument_valid = (function
                         | [(Const _) ; (Const _)] -> false
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Bool (x <= y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(<= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-geq";
    codomain = Type.BOOL;
    domain = [Type.INT;Type.INT];
    is_argument_valid = (function
                         | [(Const _) ; (Const _)] -> false
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Bool (x >= y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(>= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-eq";
    codomain = Type.BOOL;
    domain = [Type.INT;Type.INT];
    is_argument_valid = (function
                         | [(Const _) ; (Const _)] -> false
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Bool (x = y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-lt";
    codomain = Type.BOOL;
    domain = [Type.INT;Type.INT];
    is_argument_valid = (function
                         | [(Const _) ; (Const _)] -> false
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Bool (x < y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(< " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-gt";
    codomain = Type.BOOL;
    domain = [Type.INT;Type.INT];
    is_argument_valid = (function
                         | [(Const _) ; (Const _)] -> false
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Bool (x > y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(> " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]
