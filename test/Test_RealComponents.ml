open Base

open LoopInvGen

let value_of : Value.t -> float =
  function [@warning "-8"]
  | Real x -> x

let add_eval = (List.find_exn RealComponents.translation
                                ~f:(fun comp -> String.equal comp.name "real-add")).evaluate
let sub_eval = (List.find_exn RealComponents.translation
                                ~f:(fun comp -> String.equal comp.name "real-sub")).evaluate

let mult_eval = (List.find_exn RealComponents.scaling
                                 ~f:(fun comp -> String.equal comp.name "real-mult")).evaluate
let div_eval = (List.find_exn RealComponents.scaling
                                ~f:(fun comp -> String.equal comp.name "real-div")).evaluate

let eq_eval = (List.find_exn RealComponents.conditionals
                                ~f:(fun comp -> String.equal comp.name "real-eq")).evaluate
let geq_eval = (List.find_exn RealComponents.conditionals
                                ~f:(fun comp -> String.equal comp.name "real-geq")).evaluate
let leq_eval = (List.find_exn RealComponents.conditionals
                                ~f:(fun comp -> String.equal comp.name "real-leq")).evaluate
let ite_eval = (List.find_exn RealComponents.conditionals
                                ~f:(fun comp -> String.equal comp.name "real-ite")).evaluate

let add () =
  let rl = [Value.Real 3.54 ; Value.Real 7.52] in 
  let add_ret = add_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of add_ret) 11.06)
   in Alcotest.(check bool) "identical" true res

let add_zero () =
  let rl = [Value.Real 993.54 ; Value.Real 0.] in 
  let add_ret = add_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of add_ret) 993.54)
   in Alcotest.(check bool) "identical" true res

let add_neg () =
  let rl = [Value.Real 3.54 ; Value.Real (-10.1)] in 
  let add_ret = add_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of add_ret) (-6.56))
   in Alcotest.(check bool) "identical" true res


let sub () =
  let rl = [Value.Real 7.52 ; Value.Real 3.54] in 
  let sub_ret = sub_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of sub_ret) 3.98)
   in Alcotest.(check bool) "identical" true res

let sub_zero () =
  let rl = [Value.Real 7.543 ; Value.Real 0. ] in 
  let sub_ret = sub_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of sub_ret) 7.543)
   in Alcotest.(check bool) "identical" true res

let sub_neg () =
  let rl = [Value.Real 0. ; Value.Real 3.54] in 
  let sub_ret = sub_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of sub_ret) (-3.54))
   in Alcotest.(check bool) "identical" true res

let mult () =
  let rl = [Value.Real 3.54 ; Value.Real 7.52] in 
  let mult_ret = mult_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of mult_ret) 26.6208)
   in Alcotest.(check bool) "identical" true res

let mult_zero () =
  let rl = [Value.Real 3.54 ; Value.Real 0.] in 
  let mult_ret = mult_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of mult_ret) 0.)
   in Alcotest.(check bool) "identical" true res

let mult_neg () =
  let rl = [Value.Real 3.54 ; Value.Real (-5.42)] in 
  let mult_ret = mult_eval rl in
  let res = equal 0 (Core_kernel.Float.robustly_compare (value_of mult_ret) (-19.1868))
   in Alcotest.(check bool) "identical" true res

let div () = 
  let rl = [Value.Real 3. ; Value.Real 2.] in 
  let div_ret = div_eval rl in
  let res = Value.equal div_ret (Value.Real 1.5)
   in Alcotest.(check bool) "identical" true res

let div_neg () = 
  let rl = [Value.Real 3. ; Value.Real (-2.)] in 
  let div_ret = div_eval rl in
  let res = Value.equal div_ret (Value.Real (-1.5))
   in Alcotest.(check bool) "identical" true res

let eq () =
  let rl = [Value.Real 3.54 ; Value.Real 3.54] in 
  let eq_ret = eq_eval rl in
  let res = Value.equal eq_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let eq_not () =
  let rl = [Value.Real 3.54 ; Value.Real 3.59] in 
  let eq_ret = eq_eval rl in
  let res = Value.equal eq_ret (Value.Bool false)
   in Alcotest.(check bool) "identical" true res

let eq_neg () =
  let rl = [Value.Real 3.54 ; Value.Real (-3.54)] in 
  let eq_ret = eq_eval rl in
  let res = Value.equal eq_ret (Value.Bool false)
   in Alcotest.(check bool) "identical" true res

let geq () =
  let rl = [Value.Real 7.52 ; Value.Real 3.54] in 
  let geq_ret = geq_eval rl in
  let res = Value.equal geq_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let geq_eq () =
  let rl = [Value.Real 7.52 ; Value.Real 7.52] in 
  let geq_ret = geq_eval rl in
  let res = Value.equal geq_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let geq_not () =
  let rl = [Value.Real 7.52 ; Value.Real 7.54] in 
  let geq_ret = geq_eval rl in
  let res = Value.equal geq_ret (Value.Bool false)
   in Alcotest.(check bool) "identical" true res

let leq () = 
  let rl = [Value.Real 3.54 ; Value.Real 7.52] in 
  let leq_ret = leq_eval rl in
  let res = Value.equal leq_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let leq_eq () = 
  let rl = [Value.Real 7.42 ; Value.Real 7.42] in 
  let leq_ret = leq_eval rl in
  let res = Value.equal leq_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let leq_not () = 
  let rl = [Value.Real (-3.54) ; Value.Real (-7.52)] in 
  let leq_ret = leq_eval rl in
  let res = Value.equal leq_ret (Value.Bool false)
   in Alcotest.(check bool) "identical" true res

let ite () =
  let rl = [Value.Bool false ; Value.Real 3.54 ; Value.Real 7.52] in 
  let ite_ret = ite_eval rl in
  let res = Value.equal ite_ret (Value.Real 7.52)
   in Alcotest.(check bool) "identical" true res

let ite_true () =
  let rl = [Value.Bool true ; Value.Real 3.54 ; Value.Real 7.52] in 
  let ite_ret = ite_eval rl in
  let res = Value.equal ite_ret (Value.Real 3.54)
   in Alcotest.(check bool) "identical" true res




let all = [
  "add",              `Quick, add ;
  "add_zero",         `Quick, add_zero ;
  "add_neg",          `Quick, add_neg ;
  "sub",              `Quick, sub ;
  "sub_zero",         `Quick, sub_zero ;
  "sub_neg",          `Quick, sub_neg ;
  "mult",             `Quick, mult ;
  "mult_zero",        `Quick, mult_zero ;
  "mult_neg",         `Quick, mult_neg ;
  "div",              `Quick, div ;
  "div_neg",           `Quick, div_neg ;
  "eq",               `Quick, eq ;
  "eq_not",           `Quick, eq_not ;
  "eq_neg",           `Quick, eq_neg ;
  "geq",              `Quick, geq ;
  "geq_eq",           `Quick, geq_eq ;
  "geq_not",          `Quick, geq_not ;
  "leq",              `Quick, leq ;
  "leq_eq",           `Quick, leq_eq ;
  "leq_not",          `Quick, leq_not ;
  "ite",              `Quick, ite ;
  "ite_true",         `Quick, ite_true ;

]
