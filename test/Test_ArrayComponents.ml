open Base

open LoopInvGen

let equal_eval = (List.find_exn ArrayComponents.all
                                ~f:(fun comp -> String.equal comp.name "equal")).evaluate
let select_eval = (List.find_exn ArrayComponents.all
                                 ~f:(fun comp -> String.equal comp.name "select")).evaluate
let store_eval = (List.find_exn ArrayComponents.all
                                ~f:(fun comp -> String.equal comp.name "store")).evaluate

let select () =
  let arr = Value.Array (Type.INT, Type.INT, [(Value.Int 3, Value.Int 10)], Value.Int 1) in
  let select_ret = select_eval [arr; (Value.Int 3)] in
  let res = Value.equal select_ret (Value.Int 10)
   in Alcotest.(check bool) "identical" true res

let select_default () =
  let arr = Value.Array (Type.INT, Type.INT, [(Value.Int 3, Value.Int 10)], Value.Int 1) in
  let select_ret = select_eval [arr; (Value.Int 4)] in
  let res = Value.equal select_ret (Value.Int 1)
   in Alcotest.(check bool) "identical" true res

let store () =
  let arr = Value.Array((Type.INT, Type.INT, [(Value.Int 3, Value.Int 10)], Value.Int 1)) in
  let stored_arr = Value.Array (Type.INT, Type.INT,
                                [(Value.Int 4, Value.Int 4) ; (Value.Int 3, Value.Int 10)],
                                Value.Int 1) in
  let store_ret = store_eval [arr ; (Value.Int 4) ; (Value.Int 4)] in
  let res = Value.equal stored_arr store_ret
   in Alcotest.(check bool) "identical" true res

let select_double_store () =
  let arr = Value.Array (Type.INT, Type.INT, [], Value.Int 1) in
  let select_ret = select_eval [ (store_eval [ (store_eval [arr ; (Value.Int 4) ; (Value.Int 4)])
                                             ; (Value.Int 4) ; (Value.Int 10)])
                               ; (Value.Int 4)] in
  let res = Value.equal select_ret (Value.Int 10)
   in Alcotest.(check bool) "identical" true res

let equal_empty () =
  let a_arr = Value.Array (Type.INT, Type.INT, [], Value.Int 1) in
  let b_arr = Value.Array (Type.INT, Type.INT, [], Value.Int 1) in
  let equal_ret = equal_eval [a_arr ; b_arr] in
  let res = Value.equal equal_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let unequal_defaults () =
  let a_arr = Value.Array (Type.INT, Type.INT, [], Value.Int 1) in
  let b_arr = Value.Array (Type.INT, Type.INT, [], Value.Int 0) in
  let equal_ret = equal_eval [a_arr ; b_arr] in
  let res = Value.equal equal_ret (Value.Bool false)
   in Alcotest.(check bool) "identical" true res

let equal_non_empty () =
  let a_arr = Value.Array (Type.INT, Type.INT,
                           [(Value.Int 4, Value.Int 5) ; (Value.Int 10, Value.Int 5)],
                           Value.Int 1) in
  let b_arr = Value.Array (Type.INT, Type.INT,
                           [(Value.Int 4, Value.Int 5) ; (Value.Int 10, Value.Int 5)],
                           Value.Int 1) in
  let equal_ret = equal_eval [a_arr ; b_arr] in
  let res = Value.equal equal_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let equal_double_store () =
  let a_arr = Value.Array (Type.INT, Type.INT,
                           [(Value.Int 4, Value.Int 5) ; (Value.Int 10, Value.Int 5)],
                           Value.Int 1) in
  let b_arr = Value.Array (Type.INT, Type.INT,
                           [(Value.Int 4, Value.Int 5) ; (Value.Int 4, Value.Int 6) ; (Value.Int 10, Value.Int 5)],
                           Value.Int 1) in
  let equal_ret = equal_eval [a_arr ; b_arr] in
  let res = Value.equal equal_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let equal_order_independence () =
  let a_arr = Value.Array (Type.INT, Type.INT,
                           [(Value.Int 10, Value.Int 5) ; (Value.Int 4, Value.Int 5)],
                           Value.Int 1) in
  let b_arr = Value.Array (Type.INT, Type.INT,
                           [(Value.Int 4, Value.Int 5) ; (Value.Int 10, Value.Int 5)],
                           Value.Int 1) in
  let equal_ret = equal_eval [a_arr ; b_arr] in
  let res = Value.equal equal_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let all = [
  "select",                   `Quick, select ;
  "select default",           `Quick, select_default ;
  "store",                    `Quick, store ;
  "equal empty",              `Quick, equal_empty ;
  "(un)equal defaults",       `Quick, unequal_defaults ;
  "equal non-empty",          `Quick, equal_non_empty ;
  "select double store",      `Quick, select_double_store ;
  "equal double store",       `Quick, equal_double_store ;
  "equal order independence", `Quick, equal_order_independence ;
]