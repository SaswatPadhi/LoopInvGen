open Base

open Expr
open Utils

let value_of : Value.t -> float =
  function [@warning "-8"]
  | Real x -> x
  | String "" -> 0.

let translation = [
  {
    name = "real-add";
    codomain = Type.REAL;
    domain = Type.[REAL; REAL];
    is_argument_valid = Value.(function
                       | [x ; y] -> (x =/= Const (Real 0.)) && (y =/= Const (Real 0.))
                                 && (match [x ; y] with
                                     | [x ; FCall (comp, [_ ; y])]
                                       when String.equal comp.name "real-sub"
                                       -> x =/= y
                                     | [FCall (comp, [_ ; x]) ; y]
                                       when String.equal comp.name "real-sub"
                                       -> x =/= y
                                     | _ -> true)
                       | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [v1 ; v2] -> Real ((value_of v1) +. (value_of v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ a ^ "+" ^ b ^ ")")
  } ;
  {
    name = "real-sub";
    codomain = Type.REAL;
    domain = Type.[REAL; REAL];
    is_argument_valid = Value.(function
                       | [x ; y] -> (x =/= y)
                                 && (x =/= Const (Real 0.)) && (y =/= Const (Real 0.))
                                 && (match [x ; y] with
                                     | [(FCall (comp, [x ; y])) ; z]
                                       when String.equal comp.name "real-add"
                                       -> x =/= z && y =/= z
                                     | [(FCall (comp, [x ; _])) ; y]
                                       when String.equal comp.name "real-sub"
                                       -> x =/= y
                                     | [x ; (FCall (comp, [y ; _]))]
                                       when String.(equal comp.name "real-sub" || equal comp.name "real-add")
                                       -> x =/= y
                                     | _ -> true)
                       | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [v1 ; v2] -> Real ((value_of v1) -. (value_of v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ a ^ "-" ^ b ^ ")")
  }
]

let scaling = [
  {
    name = "real-mult";
    codomain = Type.REAL;
    domain = Type.[REAL; REAL];
    is_argument_valid = Value.(function
                       | [x ; y]
                         -> (x =/= Const (Real 0.)) && (x =/= Const (Real 1.)) && (x =/= Const (Real (-1.)))
                         && (y =/= Const (Real 0.)) && (y =/= Const (Real 1.)) && (x =/= Const (Real (-1.)))
                       | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [v1 ; v2] -> Real ((value_of v1) *. (value_of v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ a ^ "*" ^ b ^ ")")
  } ;
  {
    name = "real-div";
    codomain = Type.REAL;
    domain = Type.[REAL; REAL];
    is_argument_valid = Value.(function
                       | [x ; y] -> x =/= y
                                 && (x =/= Const (Real 0.)) && (x =/= Const (Real 1.)) && (x =/= Const (Real (-1.)))
                                 && (y =/= Const (Real 0.)) && (y =/= Const (Real 1.)) && (y =/= Const (Real (-1.)))
                       | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [v1 ; v2] -> Real ((value_of v1) /. (value_of v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ a ^ "/" ^ b ^ ")")
  }
]

let conditionals = [
  {
    name = "real-eq";
    codomain = Type.BOOL;
    domain = Type.[REAL; REAL];
    is_argument_valid = (function
                 | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                 | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [v1 ; v2] -> Bool Float.Approx.(equal (value_of v1) (value_of v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ a ^ "=" ^ b ^ ")")
  } ;
  {
    name = "real-geq";
    codomain = Type.BOOL;
    domain = Type.[REAL; REAL];
    is_argument_valid = (function
                 | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                 | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [v1 ; v2] -> Bool Float.Approx.(compare (value_of v1) (value_of v2) >= 0));
    to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ a ^ ">=" ^ b ^ ")")
  } ;
  {
    name = "real-leq";
    codomain = Type.BOOL;
    domain = Type.[REAL; REAL];
    is_argument_valid = (function
                 | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                 | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [v1 ; v2] -> Bool Float.Approx.(compare (value_of v1) (value_of v2) <= 0));
    to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ a ^ "<=" ^ b ^ ")")
  } ;
  {
    name = "real-ite";
    codomain = Type.REAL;
    domain = Type.[BOOL; REAL; REAL];
    is_argument_valid = (function
                 | [x ; y ; z] -> (not (is_constant x)) && (y =/= z)
                 | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Bool x ; v1 ; v2]
                      -> Real (if x then (value_of v1) else (value_of v2)));
    to_string = (fun [@warning "-8"] [a ; b ; c] -> "IF(" ^ a ^ "," ^ b ^ "," ^ c ^ ")")
  }
]



let levels = Array.accumulate_lists [| translation ; scaling ; conditionals |]

let no_bool_levels = Array.accumulate_lists [| translation ; scaling |]
