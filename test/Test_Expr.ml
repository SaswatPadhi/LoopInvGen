open Base
open LoopInvGen
open Expr
open TypeUnification

let unify_component_test () =
  let comp = {
    evaluate = (fun _ -> (Value.Int 0));
    codomain = Type.ARRAY ((Type.TVAR "a"),(Type.TVAR "b"));
    domain = [Type.ARRAY (Type.TVAR "a", Type.TVAR "b"); Type.TVAR "a"];
    to_string = (fun _ ->"");
    global_constraints = (fun _ -> []);
    name = "store";
    is_argument_valid = (fun _ -> true);
  } in
  let args = [{
    expr = Const (Value.Int 5);
    outputs = [|(Value.Array (Type.INT,Type.INT, [], (Value.Int 0)))|]
  }; 
  {
    expr = Const (Value.Int 5);
    outputs = [|(Value.Int 5)|]
  }] in
  let res = match (unify_component comp args) with
            | Some applied_comp -> begin if (Poly.equal applied_comp.codomain (Type.ARRAY (Type.INT,Type.INT))) then 
                                            begin if (List.equal Poly.equal applied_comp.domain [Type.ARRAY (Type.INT, Type.INT);Type.INT]) then true
                                                  else false
                                            end
                                        else false 
                                   end
            | None -> false
in Alcotest.(check bool) "identical" true res

let all = [
  "unify component", `Quick, unify_component_test ;
]