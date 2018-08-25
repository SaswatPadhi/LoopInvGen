open Base

open Expr

let components = let (=/=) = (fun x y -> (not (Expr.equal x y))) in [
  {
    name = "str-len";
    codomain = Type.INT;
    domain = [Type.STRING];
    is_argument_valid = (function
                         | [ x ] -> x =/= Const (Value.String "")
                         | _ -> false);
    evaluate = (function [@warning "-8"] [Value.String x] -> Value.Int (String.length x));
    to_string = (fun [@warning "-8"] [a] -> "(str.len " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ; {
    name = "str-concat";
    codomain = Type.STRING;
    domain = [Type.STRING;Type.STRING];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= Const (Value.String "")) && (y =/= Const (Value.String ""))
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.String x ; Value.String y] -> Value.String (x ^ y));
    to_string = (fun [@warning "-8"] [a ; b] -> "(str.++ " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ; {
    name = "str-contains";
    codomain = Type.BOOL;
    domain = [Type.STRING;Type.STRING];
    is_argument_valid = (function
                         | [Const _ ; Const _] -> false
                         | [(Const _) as x ; y] | [y ; (Const _) as x]
                           -> (x =/= y) && (x =/= Const (Value.String ""))
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.String x ; Value.String y]
                  -> Value.Bool (match String.substr_index x ~pattern:y with None -> false | _ -> true));
    to_string = (fun [@warning "-8"] [a ; b] -> "(str.contains " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ; {
    name = "str-prefix-of";
    codomain = Type.BOOL;
    domain = [Type.STRING;Type.STRING];
    is_argument_valid = (function
                         | [Const _ ; Const _] -> false
                         | [(Const _) as x ; y] | [y ; (Const _) as x]
                           -> (x =/= y) && (x =/= Const (Value.String ""))
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.String x ; Value.String y] -> Value.Bool (String.is_prefix y ~prefix:x));
    to_string = (fun [@warning "-8"] [a ; b] -> "(str.prefixof " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ; {
    name = "str-suffix-of";
    codomain = Type.BOOL;
    domain = [Type.STRING;Type.STRING];
    is_argument_valid = (function
                         | [Const _ ; Const _] -> false
                         | [(Const _) as x ; y] | [y ; (Const _) as x]
                           -> (x =/= y) && (x =/= Const (Value.String ""))
                         | [x ; y] -> x =/= y
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.String x ; Value.String y] -> Value.Bool (String.is_suffix y ~suffix:x));
    to_string = (fun [@warning "-8"] [a ; b] -> "(str.suffixof " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ; {
    name = "str-replace";
    codomain = Type.STRING;
    domain = [Type.STRING;Type.STRING;Type.STRING];
    is_argument_valid = (function
                         | [x ; y ; z] -> (x =/= Const (Value.String ""))
                                       && (x =/= y) && (y =/= z)
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.String x ; Value.String y ; Value.String z]
                  -> Value.String (String.substr_replace_first x ~pattern:y ~with_:z));
    to_string = (fun [@warning "-8"] [a ; b ; c] -> "(str.replace " ^ a ^ " " ^ b ^ " " ^ c ^ ")");
    global_constraints = (fun _ -> [])
  } ; {
    name = "str-at";
    codomain = Type.STRING;
    domain = [Type.STRING;Type.INT];
    is_argument_valid = (function
                         | [x ; y] -> x =/= Const (Value.String "")
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.String x ; Value.Int y] -> Value.String String.(of_char (get x y)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(str.at " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun [@warning "-8"] [a ; b] -> [ "(<= 0 " ^ b ^ ")"
                                                         ; "(< " ^ b ^ " (str.len " ^ a ^ "))" ])
  } ; {
    name = "str-substr";
    codomain = Type.STRING;
    domain = [Type.STRING;Type.INT;Type.INT];
    is_argument_valid = (function
                         | [x ; y ; z] -> x =/= Const (Value.String "")
                         | _ -> false);
    evaluate = (function [@warning "-8"]
                | [Value.String x ; Value.Int y ; Value.Int z]
                  -> Value.String (String.sub x ~pos:y ~len:z));
    to_string = (fun [@warning "-8"] [a ; b ; c] -> "(str.substr " ^ a ^ " " ^ b ^ " " ^ c ^ ")");
    global_constraints = (fun [@warning "-8"] [a ; b ; c]
                          -> [ "(<= 0 " ^ b ^ ")"
                             ; "(< (+ " ^ b ^ " " ^ c ^ ") (str.len " ^ a ^ "))" ])
  }
]