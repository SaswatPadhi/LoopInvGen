open Base
open LoopInvGen
open Type
open TypeUnification

let unify_correct () =
  let domain1 = [Type.ARRAY (Type.TVAR "'a", Type.TVAR "'b")] in
  let domain2 = [Type.ARRAY(Type.INT,Type.INT)] in
  let s = unify_types domain1 domain2 [] in
  let s_correct = [("'a", Type.INT); ("'b", Type.INT)] in
  let res = (List.equal Poly.equal s s_correct)
in Alcotest.(check bool) "identical" true res

let unify_correct_poly () =
  let domain1 = [Type.ARRAY (Type.TVAR "'a", Type.TVAR "'b"); Type.TVAR "'a"] in
  let domain2 = [Type.ARRAY(Type.STRING,Type.INT); Type.STRING] in
  let s = unify_types domain1 domain2 [] in
  let s_correct = [("'a", Type.STRING); ("'b", Type.INT)] in
  let res = (List.equal Poly.equal s s_correct)
in Alcotest.(check bool) "identical" true res

let unify_incorrect_circular () =
  let domain1 = [(TVAR "x"); ARRAY((TVAR "x",INT))] in
  let domain2 = [(ARRAY(INT,INT));ARRAY(INT,INT)] in
  let res = is_unifiable domain1 domain2
in Alcotest.(check bool) "cannot unify" false res


let unify_incorrect_self () =
  let domain1 = [(ARRAY((ARRAY(INT,(TVAR "a"))),(TVAR "a")))] in
  let domain2 = [(ARRAY((ARRAY((TVAR "b"),(TVAR "a"))),(INT)))] in
  let res = is_unifiable domain1 domain2
in Alcotest.(check bool) "cannot unify" false res

let apply_env_correct () =
  let env = [("a",INT);("b",INT)] in
  let codomain = ARRAY((TVAR "a"),(TVAR "b")) in
  let applied_codomain = ARRAY(INT,INT) in
  let res = match (apply_env env codomain) with
            | Some res -> (Poly.equal res applied_codomain)
            | None -> false
in Alcotest.(check bool) "correct application of env" true res

let apply_env_incorrect () =
  let env = [("a",INT)] in
  let codomain = ARRAY((TVAR "a"),(TVAR "b")) in
  let applied_codomain = ARRAY (INT ,INT) in
  let res = match (apply_env env codomain) with
            | Some res -> (Poly.equal res applied_codomain)
            | None -> false
in Alcotest.(check bool) "incorrect application of env" false res

let all = [
  "'a and 'b unifies",             `Quick, unify_correct ;
  "'a and 'b does not unify",      `Quick, unify_incorrect_circular ;
  "'a and 'b does not unify",      `Quick, unify_incorrect_self ;
  "'a and 'b unifies with polymorphic types",             `Quick, unify_correct_poly ;
  "codomain substitution works",   `Quick, apply_env_correct ;
  "codomain substitution does not work",    `Quick, apply_env_incorrect ;
]