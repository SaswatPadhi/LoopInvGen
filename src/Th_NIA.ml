open Base

open Expr

let pos_div x y = (x - (x % y)) / y

let components = let (=/=) = (fun x y -> (not (Expr.equal x y))) in [
  {
    name = "int-div";
    codomain = Type.INT;
    domain = [Type.INT;Type.INT];
    is_argument_valid = (function
                         | [x ; y] -> x =/= y
                                   && (x =/= Const (Value.Int 0)) && (x =/= Const (Value.Int 1))
                                   && (y =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 1))
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.Int x ; Value.Int y] when y <> 0 -> Value.Int (pos_div x y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(div " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun [@warning "-8"] [_ ; b] -> ["(not (= 0 " ^ b ^ "))"]);
  } ;
  {
    name = "int-mod";
    codomain = Type.INT;
    domain = [Type.INT;Type.INT];
    is_argument_valid = (function
                         | [x ; y] -> x =/= y
                                   && (x =/= Const (Value.Int 0)) && (x =/= Const (Value.Int 1))
                                   && (y =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 1))
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.Int x ; Value.Int y] when y <> 0 -> Value.Int (x % y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(mod " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun [@warning "-8"] [_ ; b] -> ["(not (= 0 " ^ b ^ "))"]);
  } ;
  {
    name = "nonlin-int-mult";
    codomain = Type.INT;
    domain = [Type.INT; Type.INT];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= Const (Value.Int 0)) && (x =/= Const (Value.Int 1))
                                   && (y =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 1))
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.Int x ; Value.Int y] -> Value.Int (x * y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(* " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]