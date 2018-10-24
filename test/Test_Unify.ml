open Base
open LoopInvGen

open Type
open Unify
open Utils


let unification_test () = 
  let domain1 = [TVAR "x"; LIST (TVAR "x")] in 
  let codomain1 = TVAR "x" in 
  let domain2 = [INT; LIST INT] in 
  let s = unify domain1 domain2 in 
  let codomain2 = apply s codomain1 in 
  Alcotest.(check bool) "identical" true (Poly.equal codomain2 INT);

  let domain1 = [TVAR "x"; LIST (TVAR "x")] in 
  let domain2 = [LIST INT; LIST INT] in 
  let s = unifiable domain1 domain2 in 
  Alcotest.(check bool) "identical" false s;

  let domain1 = [TVAR "x"; TVAR "x"] in 
  let domain2 = [LIST BOOL; LIST INT] in 
  let s = unifiable domain1 domain2 in 
  Alcotest.(check bool) "identical" false s;

  let domain1 = [TVAR "x"; TVAR "y"] in 
  let domain2 = [BOOL; LIST INT] in 
  let s = unifiable domain1 domain2 in 
  Alcotest.(check bool) "identical" true s;

  let names = ["x"; "y"] in 
  let domains = [TVAR "x"; LIST (TVAR "y")] in 
  let res = rename names domains in 
  Alcotest.(check (list string)) "identical" 
    (List.map ~f:Type.to_string [TVAR "x0"; LIST (TVAR "y0")]) 
    (List.map ~f:Type.to_string res)

let all = [
  "Unification Test",    `Quick, unification_test ;
]