open Base

open LoopInvGen

open Expr

let find_component list name = List.find_exn list ~f:(fun c -> String.equal c.name name)

let unify_success () =
  let select_comp = find_component ArrayComponents.all "select" in
  let arg_types = Type.[ ARRAY (STRING,INT) ; STRING ] in
  let res = Type.(match unify_component select_comp arg_types with
                  | None -> false
                  | Some unified_comp
                    -> equal unified_comp.codomain INT
                    && (List.equal equal unified_comp.domain [ARRAY (STRING, INT) ; STRING]))
   in Alcotest.(check bool) "identical" true res

let unify_failure () =
  let select_comp = find_component ArrayComponents.all "select" in
  let arg_types = Type.[ ARRAY (STRING,INT) ; INT ] in
  let res = unify_component select_comp arg_types
   in Alcotest.(check bool) "identical" true (Option.is_none res)

let transformed () =
  let list_comps = ListComponents.all_transformed_int_binary in
  let hd_comp = find_component list_comps "hd" in
  let map_fixR_ge_comp = find_component list_comps "map-fixR-int-geq" in
  let res = Type.(match unify_component hd_comp [map_fixR_ge_comp.codomain] with
                  | None -> false
                  | Some unified_comp
                    -> equal unified_comp.codomain BOOL
                    && (List.equal equal unified_comp.domain [ LIST BOOL ]))
   in Alcotest.(check bool) "identical" true res

let all = [
  "Successful unification",   `Quick, unify_success ;
  "Unsuccessful unification", `Quick, unify_failure ;
  "Transformed component",    `Quick, transformed ;
]