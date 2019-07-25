open Base

open Expr

let all = [
  (* {
    name = "select";
    codomain = Type.INT;
    domain = [Type.ARRAY (Type.INT,Type.INT); Type.INT];
    is_argument_valid = (function                         
                         | _ -> true);
    evaluate = (function [@warning "-8"]
                [Value.Array (_, _, elems, default_val) ; Value.Int key]
                -> match List.Assoc.find elems ~equal:Value.equal (Value.Int key) with
                   | None -> default_val
                   | Some value -> value);                                                                              
    to_string = (fun [@warning "-8"] [a ; b] -> "(select " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }; 
   *)
  {
    name = "select0";
    codomain = Type.INT;
    domain = [Type.ARRAY (Type.INT,Type.INT)];
    is_argument_valid = (function
                         | _ -> true);
    evaluate = (function [@warning "-8"]
                [Value.Array (_, _, elems, default_val)]
                -> match List.Assoc.find elems ~equal:Value.equal (Value.Int 0) with
                   | None -> default_val
                   | Some value -> value);
    to_string = (fun [@warning "-8"] [a] -> "(select " ^ a ^ " 0)");
    global_constraints = (fun _ -> [])
  }; 
  
  {
    name = "store";
    codomain = Type.ARRAY (Type.INT,Type.INT);
    domain = [Type.ARRAY (Type.INT,Type.INT); Type.INT; Type.INT];
    is_argument_valid = (function                         
                         | _ -> true);
    evaluate = (function [@warning "-8"] [Value.Array (key_type, val_type, elems, default_val) ; Value.Int key; Value.Int value] -> Value.Array (key_type,val_type, (Value.Int key, Value.Int value)::elems,default_val));
    to_string = (fun [@warning "-8"] [a ; b ; c] -> "(store " ^ a ^ " " ^ b ^ " " ^ c ^")");
    global_constraints = (fun _ -> [])
  }

]
