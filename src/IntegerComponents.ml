open Base

open Expr

let pos_div x y = (x - (x % y)) / y

let equality = [
  {
    name = "int-eq";
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Bool (x = y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let intervals = equality @ [
   {
    name = "int-geq";
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Bool (x >= y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(>= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-leq";
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Bool (x <= y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(<= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-lt";
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Bool (x < y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(< " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-gt";
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Bool (x > y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(> " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let octagons = intervals @ [
  {
    name = "int-add";
    codomain = Type.INT;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; FCall (comp, [_ ; y])]
                           when String.equal comp.name "int-sub"
                           -> x =/= y && (x =/= Const (Value.Int 0))
                         | [FCall (comp, [_ ; x]) ; y]
                           when String.equal comp.name "int-sub"
                           -> x =/= y && (y =/= Const (Value.Int 0))
                         | [x ; y] -> (x =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 0))
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Int (x + y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(+ " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "int-sub";
    codomain = Type.INT;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [(FCall (comp, [x ; y])) ; z]
                           when String.equal comp.name "int-add"
                           -> x =/= z && y =/= z && (z =/= Const (Value.Int 0))
                         | [(FCall (comp, [x ; _])) ; y]
                           when String.equal comp.name "int-sub"
                           -> x =/= y && (y =/= Const (Value.Int 0))
                         | [x ; (FCall (comp, [y ; _]))]
                           when (String.equal comp.name "int-sub" || String.equal comp.name "int-add")
                           -> x =/= y
                         | [x ; y] -> (x =/= y)
                                   && (x =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 0))
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Int (x - y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(- " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let polyhedra = octagons @ [
  {
    name = "int-lin-mult";
    codomain = Type.INT;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y]
                           -> (x =/= Const (Value.Int 0)) && (x =/= Const (Value.Int 1))
                           && (y =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 1))
                           && (is_constant x || is_constant y)
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Int (x * y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(* " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let polynomials = polyhedra @ [
  {
    name = "int-nonlin-mult";
    codomain = Type.INT;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y] -> not (is_constant x || is_constant y)
                         | _ -> false);
    evaluate = (function [@warning "-8"] Value.[Int x ; Int y] -> Value.Int (x * y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(* " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let peano = polynomials @ [
  {
    name = "int-div";
    codomain = Type.INT;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y] -> x =/= y
                                   && (x =/= Const (Value.Int 0)) && (x =/= Const (Value.Int 1))
                                   && (y =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 1))
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | Value.[Int x ; Int y] when y <> 0 -> Value.Int (pos_div x y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(div " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun [@warning "-8"] [_ ; b] -> ["(not (= 0 " ^ b ^ "))"]);
  } ;
  {
    name = "int-mod";
    codomain = Type.INT;
    domain = Type.[INT; INT];
    is_argument_valid = (function
                         | [x ; y] -> x =/= y
                                   && (x =/= Const (Value.Int 0)) && (x =/= Const (Value.Int 1))
                                   && (y =/= Const (Value.Int 0)) && (y =/= Const (Value.Int 1))
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | Value.[Int x ; Int y] when y <> 0 -> Value.Int (x % y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(mod " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun [@warning "-8"] [_ ; b] -> ["(not (= 0 " ^ b ^ "))"]);
  }
]

let linear_levels = [| equality ; intervals ; octagons ; polyhedra |]
let non_linear_levels = [| equality ; intervals ; octagons ; polyhedra ; polynomials ; peano |]