open Base
open LoopInvGen
open PIE
open TestGen

let len_job = Job.create
    ~f:(fun [@warning "-8"] [ Value.List(l,_) ] -> Value.Bool (List.length l < 2))
    ~args:([ "x", Type.LIST Type.INT ])
    ~post:(fun inp res -> match inp , res with
        | [ Value.List (_, _) ], Ok (Value.Bool y) -> y
        | _ -> false)
    (List.map [[]; [1]; [2;2]; [3]; [4;1;0]]
       ~f:(fun l ->
           let vi = List.map l ~f:(fun i -> Value.Int i) in
           [Value.List (vi, Type.INT)]))

let list_eq_job = Job.create
    ~f:(fun [@warning "-8"] [l]  -> l)
    ~args:([ "x", Type.LIST Type.INT ])
    ~post:(fun inp res -> match inp , res with
        | _, Ok v -> Value.equal v (Value.List ([Value.Int 0; Value.Int 0; Value.Int 0], Type.INT) )
        | _ -> false)
    (repeat ~n:1000
       [for_type (Type.LIST Type.INT) ~s:{list_dim = [2--5]; int_range = 0--1} ])

let test_gen_test () = 
    let s = {list_dim = [weighted 1 5]; int_range = (-1)--1} in
    let l = repeat ~n:100 ~seed:"test" [for_type ~s (Type.LIST Type.INT)] in
    (* let printl l = List.iter l 
        ~f:(fun x -> Stdio.print_endline (Value.to_string (List.hd_exn x))) in
    printl gen; *)
    (* This should be weighted so more 5s then 4s and so on *)
    let countlen len =
      List.count l ~f:(fun l1 -> match l1 with
          | [Value.List (l,_)] -> List.length l = len
          | _ -> false) in
    Alcotest.(check bool) "identical" true
        (List.for_all (List.init 4 ~f:(fun n -> countlen (n+2) > countlen (n+1))) ~f:(fun x -> x))

let len_test () =
  let res = cnf_opt_to_desc (learnPreCond len_job) in
  Alcotest.(check string) "identical" "(<= (len x) 1)" res

let list_eq_test () =
  let res = cnf_opt_to_desc (learnPreCond list_eq_job) in
  Alcotest.(check string) "identical" "(eq (0 :: (0 :: (0 :: ()))) x)" res

let mk_silent_test job () =
  let res = cnf_opt_to_desc (learnPreCond job) in
  Stdio.print_endline ("result = " ^ res);
  Alcotest.(check bool) "identical" true true

let all = [
  "List.len <= 2", `Quick, len_test;
  "List.equal [0; 0; 0]", `Quick, list_eq_test;
  "TestGen works", `Quick, test_gen_test;
]