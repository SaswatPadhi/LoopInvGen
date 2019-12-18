open Core

open LoopInvGen

open Exceptions
open Type

let are_bindings_equal =
  List.equal (Tuple.T2.equal ~eq1:String.equal ~eq2:equal)

let monomorphic () =
  let domain1 = [ INT ; STRING ] in
  let domain2 = [ INT ; STRING ] in
  let bindings = Unification.of_types_exn domain1 domain2 in
  let bindings_correct = [] in
  let res = are_bindings_equal bindings bindings_correct
   in Alcotest.(check bool) "identical" true res

let without_dependencies () =
  let domain1 = [ ARRAY (TVAR "a", TVAR "b") ; INT ; STRING ] in
  let domain2 = [ ARRAY (INT,BOOL) ; INT ; STRING ] in
  let bindings = Unification.of_types_exn domain1 domain2 in
  let bindings_correct = [("a", INT); ("b", BOOL)] in
  let res = are_bindings_equal bindings bindings_correct
   in Alcotest.(check bool) "identical" true res

let with_dependencies () =
  let domain1 = [ ARRAY (TVAR "a", TVAR "b") ; LIST(TVAR "a") ] in
  let domain2 = [ ARRAY (STRING,INT) ; LIST STRING ] in
  let bindings = Unification.of_types_exn domain1 domain2 in
  let correct_bindings = [("a", STRING) ; ("b", INT)] in
  let res = are_bindings_equal bindings correct_bindings
   in Alcotest.(check bool) "identical" true res

let indirect_circular () =
  let domain1 = [(TVAR "x") ; ARRAY(TVAR "x",INT)] in
  let domain2 = [(ARRAY(INT,INT)) ; ARRAY(INT,INT)] in
  let test () = ignore (Unification.of_types_exn domain1 domain2)
   in Alcotest.check_raises "cannot unify" (Unification_Exn "Circular dependency!") test

let direct_circular () =
  let domain1 = [ ARRAY (ARRAY(INT,TVAR "a") , TVAR "a") ] in
  let domain2 = [ ARRAY (ARRAY(TVAR "b",TVAR "a") , INT) ] in
  let test () = ignore (Unification.of_types_exn domain1 domain2)
   in Alcotest.check_raises "cannot unify" (Unification_Exn "Circular dependency!") test

let substitution () =
  let env = [("a",STRING) ; ("b",INT)] in
  let codomain = ARRAY(TVAR "b" , TVAR "a") in
  let resolved_codomain = ARRAY(INT,STRING) in
  let res = match Unification.substitute env codomain with
            | Some res -> equal res resolved_codomain
            | None -> false
   in Alcotest.(check bool) "correct application of env" true res

let incomplete_substitution () =
  let env = [("a",INT)] in
  let codomain = ARRAY(TVAR "a" , TVAR "b") in
  let resolved_codomain = ARRAY (INT ,INT) in
  let res = match Unification.substitute env codomain with
            | Some res -> equal res resolved_codomain
            | None -> false
   in Alcotest.(check bool) "incorrect application of env" false res

let all = [
  "Unif. of monomorphic types",   `Quick, monomorphic ;
  "Unif. without dependencies",   `Quick, without_dependencies ;
  "Unif. with dependencies",      `Quick, with_dependencies ;
  "Direct circular dependency",   `Quick, direct_circular ;
  "Indirect circular dependency", `Quick, indirect_circular ;
  "Substitution",                 `Quick, substitution ;
  "Incomplete substitution",      `Quick, incomplete_substitution ;
]