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
  let res = Value.equal (Value.Int 0) (Value.Int (Core_kernel.Float.robustly_compare (value_of add_ret) 11.06))
   in Alcotest.(check bool) "identical" true res

let sub () =
  let rl = [Value.Real 7.52 ; Value.Real 3.54] in 
  let sub_ret = sub_eval rl in
  let res = Value.equal (Value.Int 0) (Value.Int (Core_kernel.Float.robustly_compare (value_of sub_ret) 3.98))
   in Alcotest.(check bool) "identical" true res

let mult () =
  let rl = [Value.Real 3.54 ; Value.Real 7.52] in 
  let mult_ret = mult_eval rl in
  let res = Value.equal (Value.Int 0) (Value.Int (Core_kernel.Float.robustly_compare (value_of mult_ret) 26.6208))
   in Alcotest.(check bool) "identical" true res

let div () = 
  let rl = [Value.Real 3. ; Value.Real 2.] in 
  let div_ret = div_eval rl in
  let res = Value.equal div_ret (Value.Real 1.5)
   in Alcotest.(check bool) "identical" true res

let eq () =
  let rl = [Value.Real 3.54 ; Value.Real 3.54] in 
  let eq_ret = eq_eval rl in
  let res = Value.equal eq_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res
  

let geq () =
  let rl = [Value.Real 7.52 ; Value.Real 3.54] in 
  let geq_ret = geq_eval rl in
  let res = Value.equal geq_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let leq () = 
  let rl = [Value.Real 3.54 ; Value.Real 7.52] in 
  let leq_ret = leq_eval rl in
  let res = Value.equal leq_ret (Value.Bool true)
   in Alcotest.(check bool) "identical" true res

let ite () =
  let rl = [Value.Bool false ; Value.Real 3.54 ; Value.Real 7.52] in 
  let ite_ret = ite_eval rl in
  let res = Value.equal ite_ret (Value.Real 7.52)
   in Alcotest.(check bool) "identical" true res


let all = [
  "add",              `Quick, add ;
  "sub",              `Quick, sub ;
  "mult",              `Quick, mult ;
  "div",              `Quick, div ;
  "eq",               `Quick, eq ;
  "geq",              `Quick, geq ;
  "leq",              `Quick, leq ;
  "ite",              `Quick, ite ;

]
