open Core

open Expr
open Utils

let normalize = List.dedup_and_stable_sort ~which_to_keep:`First
                                           ~compare:(fun (k1,_) (k2,_) -> Value.compare k1 k2)

let all = [
  {
    name = "select";
    codomain = Type.TVAR "b";
    domain = Type.[ARRAY (TVAR "a", TVAR "b"); TVAR "a"];
    is_argument_valid = (function
                         | [FCall (comp, [a ; k1 ; _]) ; k2]
                           when String.equal comp.name "store"
                           -> k1 =/= k2
                         | _ -> true);
    evaluate = (fun [@warning "-8"]
                Value.[Array (_, _, elems, default_val) ; key]
                -> match List.Assoc.find elems ~equal:Value.equal key with
                   | None -> default_val
                   | Some value -> value);
    to_string = (fun [@warning "-8"] [a ; b] -> "(select " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "store";
    codomain = Type.(ARRAY (TVAR "a", TVAR "b"));
    domain = Type.[ARRAY (TVAR "a", TVAR "b"); TVAR "a"; TVAR "b"];
    is_argument_valid = (function
                         | _ -> true);
    evaluate = (fun [@warning "-8"]
                Value.[Array (key_type, val_type, elems, default_val) ; key ; value]
                -> Value.Array (key_type, val_type, (key, value)::elems, default_val));
    to_string = (fun [@warning "-8"] [a ; b ; c] -> "(store " ^ a ^ " " ^ b ^ " " ^ c ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "equal";
    codomain = Type.BOOL;
    domain = Type.[ARRAY (TVAR "a", TVAR "b"); ARRAY (TVAR "a", TVAR "b")];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y)
                         | _ -> true);
    evaluate = (fun [@warning "-8"]
                Value.[ Array (a_key_type, a_val_type, a_elems, a_default_val)
                      ; Array (b_key_type, b_val_type, b_elems, b_default_val) ]
                -> Value.Bool (
                     (Type.equal a_key_type b_key_type) &&
                     (Type.equal a_val_type b_val_type) &&
                     (Value.equal a_default_val b_default_val) &&
                     (List.equal (Tuple.T2.equal ~eq1:Value.equal ~eq2:Value.equal)
                                 (normalize a_elems)
                                 (normalize b_elems))));
    to_string = (fun [@warning "-8"] [a ; b] -> "(= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let levels = [| all |]