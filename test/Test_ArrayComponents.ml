open Base
open LoopInvGen

let select_test () =
 let arr = Value.Array((Type.INT, Type.INT, [ (Value.Int 3, Value.Int 10)], Value.Int 1))
 in let select_eval = (Array.of_list ArrayComponents.all).(0).evaluate
 in let select_ret = (select_eval [arr; (Value.Int 3)])
 in let res = (Poly.equal select_ret (Value.Int 10))
 in Alcotest.(check bool) "identical" true res

let select_default_test () =
 let arr = Value.Array((Type.INT, Type.INT, [ (Value.Int 3, Value.Int 10)], Value.Int 1))
 in let select_eval = (Array.of_list ArrayComponents.all).(0).evaluate
 in let select_ret = (select_eval [arr; (Value.Int 4)])
 in let res = (Poly.equal select_ret (Value.Int 1))
 in Alcotest.(check bool) "identical" true res

let store_test () =
 let arr = Value.Array((Type.INT, Type.INT, [ (Value.Int 3, Value.Int 10)], Value.Int 1))
 in let stored_arr = Value.Array((Type.INT, Type.INT, [ (Value.Int 4, Value.Int 4) ; (Value.Int 3, Value.Int 10)], Value.Int 1))
 in let store_eval = (Array.of_list ArrayComponents.all).(1).evaluate
 in let store_ret = (store_eval [arr; (Value.Int 4); (Value.Int 4)])
 in let res = (Poly.equal stored_arr store_ret)
 in Alcotest.(check bool) "identical" true res

let select_sem_test () =
 let arr = Value.Array((Type.INT, Type.INT, [], Value.Int 1))
 in let store_eval = (Array.of_list ArrayComponents.all).(1).evaluate
 in let select_eval = (Array.of_list ArrayComponents.all).(0).evaluate
 in let select_ret = (select_eval [(store_eval [(store_eval [arr; (Value.Int 4); (Value.Int 4)]) ; (Value.Int 4) ; (Value.Int 10)]); (Value.Int 4)])
 in let res = (Poly.equal select_ret (Value.Int 10))
 in Alcotest.(check bool) "identical" true res

let equal_test () =
 let a_arr = Value.Array((Type.INT, Type.INT, [], Value.Int 1))
 in let b_arr = Value.Array((Type.INT, Type.INT, [], Value.Int 1))
 in let equal_eval = (Array.of_list ArrayComponents.all).(2).evaluate
 in let equal_ret = (equal_eval [a_arr; b_arr])
 in let res = (Poly.equal equal_ret (Value.Bool true))
 in Alcotest.(check bool) "identical" true res

let un_def_equal_test () =
 let a_arr = Value.Array((Type.INT, Type.INT, [], Value.Int 1))
 in let b_arr = Value.Array((Type.INT, Type.INT, [], Value.Int 0))
 in let equal_eval = (Array.of_list ArrayComponents.all).(2).evaluate
 in let equal_ret = (equal_eval [a_arr; b_arr])
 in let res = (Poly.equal equal_ret (Value.Bool false))
 in Alcotest.(check bool) "identical" true res

let equal_arr_elems_test () =
 let a_arr = Value.Array((Type.INT, Type.INT, [(Value.Int 4, Value.Int 5);(Value.Int 10, Value.Int 5)], Value.Int 1))
 in let b_arr = Value.Array((Type.INT, Type.INT, [(Value.Int 4, Value.Int 5);(Value.Int 10, Value.Int 5)], Value.Int 1))
 in let equal_eval = (Array.of_list ArrayComponents.all).(2).evaluate
 in let equal_ret = (equal_eval [a_arr; b_arr])
 in let res = (Poly.equal equal_ret (Value.Bool true))
 in Alcotest.(check bool) "identical" true res

let order_indp_equal_arr_elems_test () =
 let a_arr = Value.Array((Type.INT, Type.INT, [(Value.Int 10, Value.Int 5);(Value.Int 4, Value.Int 5)], Value.Int 1))
 in let b_arr = Value.Array((Type.INT, Type.INT, [(Value.Int 4, Value.Int 5);(Value.Int 10, Value.Int 5)], Value.Int 1))
 in let equal_eval = (Array.of_list ArrayComponents.all).(2).evaluate
 in let equal_ret = (equal_eval [a_arr; b_arr])
 in let res = (Poly.equal equal_ret (Value.Bool true))
 in Alcotest.(check bool) "identical" true res

let all = [
  "select array component",                  `Quick, select_test ;
  "select default in array component",       `Quick, select_default_test ;
  "store array component",                   `Quick, store_test ;
  "check two equal arrays",                  `Quick, equal_test ;
  "check two un-equal default value arrays", `Quick, un_def_equal_test ;
  "check two equal arrays with elements",    `Quick, equal_arr_elems_test ;
  "select after storing twice in the same index", `Quick, select_sem_test ;
  "check two equal arrays with elements in different order",    `Quick, order_indp_equal_arr_elems_test ;
]