open Base

open LoopInvGen

open Expr

let mock_store_component = {
  name = "mock-store";
  codomain = Type.ARRAY (Type.TVAR "a" , Type.TVAR "b");
  domain = [Type.ARRAY (Type.TVAR "a", Type.TVAR "b") ; Type.TVAR "a"];
  is_argument_valid = (fun _ -> true);
  evaluate = (fun _ -> (Value.Int 0));
  to_string = (fun _ -> "");
  global_constraints = (fun _ -> []);
}

let unify_component_test () =
  let arg_types = [ Type.ARRAY (Type.STRING,Type.INT) ; Type.STRING ] in
  let res = match unify_component mock_store_component arg_types with
    | None -> false
    | Some unified_comp
      -> Type.equal unified_comp.codomain (Type.ARRAY (Type.STRING,Type.INT))
      && (List.equal Type.equal unified_comp.domain [Type.ARRAY (Type.STRING, Type.INT) ; Type.STRING])
   in Alcotest.(check bool) "identical" true res

let all = [
  "Component unification", `Quick, unify_component_test ;
]