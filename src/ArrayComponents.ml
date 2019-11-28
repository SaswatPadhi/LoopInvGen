open Base

open Expr
open Utils

let array_key_compare (k1,_) (k2,_) = Value.compare k1 k2

let all = [
  {
    name = "select";
    codomain = Type.TVAR ("'b");
    domain = [Type.ARRAY (Type.TVAR "'a", Type.TVAR "'b"); Type.TVAR "'a"];
    is_argument_valid = (function
                         | _ -> true);
    evaluate = (function [@warning "-8"]
                [Value.Array (_, _, elems, default_val) ; key]
                -> match List.Assoc.find elems ~equal:Value.equal key with
                   | None -> default_val
                   | Some value -> value);
    to_string = (fun [@warning "-8"] [a ; b] -> "(select " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
  ;
  {
    name = "store";
    codomain = Type.ARRAY (Type.TVAR "'a", Type.TVAR "'b");
    domain = [Type.ARRAY (Type.TVAR "'a", Type.TVAR "'b"); Type.TVAR "'a"; Type.TVAR "'b"];
    is_argument_valid = (function
                         | _ -> true);
    evaluate = (function [@warning "-8"]
                [Value.Array (key_type, val_type, elems, default_val) ; key; value]
                -> Value.Array (key_type,val_type, (key, value)::elems,default_val));
    to_string = (fun [@warning "-8"] [a ; b ; c] -> "(store " ^ a ^ " " ^ b ^ " " ^ c ^ ")");
    global_constraints = (fun _ -> [])
  }

  ;
  {
    name = "equal";
    codomain = Type.BOOL;
    domain = [Type.ARRAY (Type.TVAR "'a", Type.TVAR "'b"); Type.ARRAY (Type.TVAR "'a", Type.TVAR "'b")];
    is_argument_valid = (function
                         | _ -> true);
    evaluate = (function [@warning "-8"]
                [Value.Array (a_key_type, a_val_type, a_elems, a_default_val) ; Value.Array (b_key_type, b_val_type, b_elems, b_default_val)]
                -> let dedup_a = (List.dedup_and_stable_sort a_elems ~which_to_keep:`First ~compare:array_key_compare)
                   in  let dedup_b = (List.dedup_and_stable_sort b_elems ~which_to_keep:`First ~compare:array_key_compare)
                   in Value.Bool (   (Poly.equal a_key_type b_key_type)
                                  && (Poly.equal a_val_type b_val_type)
                                  && (Poly.equal a_default_val b_default_val)
                                  && (Poly.equal dedup_a dedup_b)));
    to_string = (fun [@warning "-8"] [a ; b ] -> "(= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }

]
