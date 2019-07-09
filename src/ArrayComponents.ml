open Base

open Expr

let all = [
  {
    name = "select";
    codomain = Type.INT;
    domain = [Type.ARRAY (Type.INT,Type.INT); Type.INT];
    is_argument_valid = (function                         
                         | _ -> true);
    evaluate = (function [@warning "-8"] [Value.Array (x,y); Value.Int z] -> 
                                                                              (* (let rec lookup x z y = match x with  
                                                                                                    | [] -> y 
                                                                                                    | (z',v)::t -> (if z=z' then v else (lookup t z y))
                                                                              in Value.Int (lookup x z y))); *)
                                                                            Value.Int (z));
    to_string = (fun [@warning "-8"] [a ; b] -> "(select " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }; 


]
