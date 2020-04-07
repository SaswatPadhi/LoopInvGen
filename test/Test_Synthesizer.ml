open Base

open LoopInvGen

open Synthesizer

let plus_x_y () =
  let result = solve {
    arg_names = [ "x" ; "y" ];
    inputs = List.map ~f:(Array.map ~f:(fun i -> Value.Int i))
               [ [| 3 ; 7 ; (-1) ; (-4) |]
               ; [| 3 ; 2 ; 13 ; 11 |] ];
    outputs = Array.map ~f:(fun i -> Value.Int i) [| 6 ; 9 ; 12 ; 7 |];
    constants = []
  } in Alcotest.(check string) "identical" "(+ x y)" result.string

let ge_plus_x_z_y () =
  let result = solve {
    arg_names = [ "x" ; "y" ; "z" ];
    inputs = List.map ~f:(Array.map ~f:(fun i -> Value.Int i))
               [ [| 3 ; 7 ; (-1) ; (-4) ; 6 |]
               ; [| 9 ; (-3) ; (-10) ; 11 ; (-1)  |]
               ; [| 7 ; (-20) ; (-50) ; 11 ; (-1) |] ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| true ; false ; false ; false ; true |];
    constants = []
  } in Alcotest.(check string) "identical" "(>= (+ x z) y)" result.string

let not_or_eq_w_x_eq_y_z () =
  let result = solve {
    arg_names = [ "w" ; "x" ; "y" ; "z" ];
    inputs = List.map ~f:(Array.map ~f:(fun i -> Value.Int i))
               [ [| 4 ; (-1) ; (-5) ; 1 ; (-1) ; 2 |]
               ; [| 3 ; 7 ; (-1) ; (-4) ; 1 ; 2 |]
               ; [| 9 ; (-3) ; (-10) ; 11 ; (-10) ; 2  |]
               ; [| 1 ; (-6) ; (-10) ; 11 ; (-1) ; (-3) |] ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| true ; true ; false ; false ; true ; false |];
    constants = []
  } in Alcotest.(check string) "identical" "(not (or (= w x) (= y z)))" result.string

let select_a_k () =
  let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } {
    arg_names = [ "a" ; "k" ];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Value.Array (a,b,c,d))
                 [| (Type.INT, Type.STRING,
                     [ (Int 3, String "30")
                     ; (Int 2, String "20")
                     ; (Int 1, String "10") ],
                     String "1")
                  ; (Type.INT, Type.STRING,
                     [ (Int 2, String "20")
                     ; (Int 1, String "1024") ],
                     String "0")
                  ; (Type.INT, Type.STRING,
                     [ (Int 0, String "0") ],
                     String "30") |]);
      [| Int 1 ; Int 2 ; Int 3 |] ];
    outputs = Value.[| String "10" ; String "20" ; String "30" |];
    constants = []
  } in Alcotest.(check string) "identical" "(select a k)" result.string

let select_a_k__with_duplicates () =
  let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } {
    arg_names = [ "a" ; "k" ];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
                 [| (Type.INT, Type.INT,
                     [ (Int 3, Int 10) ; (Int 3, Int 30) ; (Int 2, Int 20) ; (Int 1, Int 10) ],
                     Int 1)
                  ; (Type.INT, Type.INT,
                     [ (Int 2, Int 20) ; (Int 1, Int 1024) ],
                     Int 0)
                  ; (Type.INT, Type.INT,
                     [ (Int 0 , Int 0)],
                     Int 30) |]);
      [| Int 3 ; Int 2 ; Int 3 |] ];
    outputs = Value.[| Int 10 ; Int 20 ; Int 30 |];
    constants = []
  } in Alcotest.(check string) "identical" "(select a k)" result.string

let store_a_k_v__empty () =
let open Synthesizer in
let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } {
  arg_names = [ "a" ; "k" ; "v"];
  inputs = Value.[
    (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
               [| (Type.INT, Type.INT, [], Int 1)
                ; (Type.INT, Type.INT, [], Int 0)
                ; (Type.INT, Type.INT, [], Int 30) |]);
    [| Int 1 ; Int 2 ; Int 3 |];
    [| Int 20 ; Int 40 ; Int 6 |] ];
  outputs = Value.[| Array (Type.INT, Type.INT, [ (Int 1, Int 20) ], Int 1)
                   ; Array (Type.INT, Type.INT, [ (Int 2, Int 40) ], Int 0)
                   ; Array (Type.INT, Type.INT, [ (Int 3, Int 6) ], Int 30) |];
  constants = []
} in Alcotest.(check string) "identical" "(store a k v)" result.string

let store_a_k_v__nonempty () =
  let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } {
    arg_names = [ "a" ; "k" ; "v"];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
                 [| (Type.INT, Type.INT, [ (Int 3, Int 20) ], Int 1)
                  ; (Type.INT, Type.INT, [ (Int 6, Int 20) ], Int 0)
                  ; (Type.INT, Type.INT, [ (Int 1, Int 20) ], Int 30) |]);
      [| Int 1 ; Int 2 ; Int 3 |];
      [| Int 20 ; Int 40 ; Int 6 |] ];
    outputs = Value.[| Array (Type.INT, Type.INT,
                              [ (Int 1, Int 20) ; (Int 3, Int 20) ],
                              Int 1)
                     ; Array (Type.INT, Type.INT,
                              [ (Int 2, Int 40) ; (Int 6, Int 20) ],
                              Int 0)
                     ; Array (Type.INT, Type.INT,
                              [ (Int 3, Int 6) ; (Int 1, Int 20) ],
                              Int 30) |];
    constants = []
  } in Alcotest.(check string) "identical" "(store a k v)" result.string

let store_a_k_v__with_duplicates () =
  let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } {
    arg_names = [ "a" ; "k" ; "v"];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
                 [| (Type.INT, Type.INT, [ (Int 3, Int 20) ], Int 1)
                  ; (Type.INT, Type.INT, [ (Int 6, Int 20) ], Int 0)
                  ; (Type.INT, Type.INT, [ (Int 1, Int 20) ], Int 30) |]);
      [| Int 3 ; Int 2 ; Int 3 |];
      [| Int 10 ; Int 40 ; Int 6 |] ];
    outputs = Value.[| Array (Type.INT, Type.INT,
                              [ (Int 3, Int 10) ; (Int 3, Int 20) ],
                              Int 1)
                     ; Array (Type.INT, Type.INT,
                              [ (Int 2, Int 40) ; (Int 6, Int 20) ],
                              Int 0)
                     ; Array (Type.INT, Type.INT,
                              [ (Int 3 , Int 6) ; (Int 1, Int 20) ],
                              Int 30) |];
    constants = []
  } in Alcotest.(check string) "identical" "(store a k v)" result.string

let ge_y_len_x () =
  let open Synthesizer in
  let result = solve ~config:{ Config.default with logic = Logic.of_string "ALL" } {
    arg_names = [ "x" ; "y" ];
    inputs = Value.[
      Array.map ~f:(fun l -> List (Type.INT, (List.map l ~f:(fun i -> Int i))))
                [| [1; (-1); 2]
                 ; [1; (-1); 2]
                 ; [1; (-1); 2]
                 ; [3]
                 ; [1]
                 ; [2] |];
      Array.map ~f:(fun i -> Int i)
                [| 2; 3; 4; 5; 0; (-1) |];
    ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| false; true; true; true; false; false |];
    constants = []
  } in Alcotest.(check string) "identical" "(>= y (len x))" result.string

let all_mapR_ge_l_0 () =
  let open Synthesizer in
  let result = solve ~config:{ Config.default with logic = Logic.of_string "ALL" } {
    arg_names = [ "l" ];
    inputs = Value.[
      Array.map ~f:(fun l -> List (Type.INT, (List.map l ~f:(fun i -> Int i))))
                [| [11; (-1); 0]
                 ; [7; 3; 1]
                 ; [2; (-3)]
                 ; [2]
                 ; [0; 1; 3; 6]
                 ; [(-1); 1; 9]
                 ; [] |]
    ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| false; true; false; true; true; false; true |];
    constants = []
  } in Alcotest.(check string) "identical" "(all (map-fixR-int-geq l 0))" result.string

let bvadd_a_b () =
  let result = solve ~config:{ Config.default with logic = Logic.of_string "BV" } {
    arg_names = ["a"; "b"];
    inputs = List.map ~f:(fun a -> Array.map ~f:(fun x -> Value.BitVec (Bitarray.of_string x)) a)
    [ [| "#b00"; "#b01" ; "#b10" ; "#b11" |] ;
      [| "#b01"; "#b10" ; "#b11" ; "#b00"|]];
    outputs = Array.map ~f:(fun x -> Value.BitVec (Bitarray.of_string x))
    [| "#b01"; "#b11"; "#b01" ; "#b11" |];
    constants = []
  } in Alcotest.(check string) "identical" "(bvadd a b)" result.string

let bvult_a_b () =
  let result = solve ~config:{ Config.default with logic = Logic.of_string "BV" } {
    arg_names = ["a"; "b"];
    inputs = List.map ~f:(fun a -> Array.map ~f:(fun x -> Value.BitVec (Bitarray.of_string x)) a)
    [ [| "#b00"; "#b01" ; "#b10" ; "#b11"|] ;
      [| "#b01"; "#b10" ; "#b11" ; "#b00"|]];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
    [|true; true; true; false|];
    constants = []
  } in Alcotest.(check string) "identical" "(bvult a b)" result.string

let bvnot_bvsub_a_b () =
  let result = solve ~config:{ Config.default with logic = Logic.of_string "BV" } {
    arg_names = ["a"; "b"];
    inputs = List.map ~f:(fun a -> Array.map ~f:(fun x -> Value.BitVec (Bitarray.of_string x)) a)
    [ [| "#b0000"; "#b0010" ; "#b1000" ; "#b1100"|] ;
      [| "#b0100"; "#b1000" ; "#b1100" ; "#b0000"|]];
    outputs = Array.map ~f:(fun x -> Value.BitVec (Bitarray.of_string x))
    [|"#b0011"; "#b0101"; "#b0011"; "#b0011"|];
    constants = []
  } in Alcotest.(check string) "identical" "(bvnot (bvsub a b))" result.string

let all = [
  "(+ x y)",                         `Quick, plus_x_y ;
  "(>= (+ x z) y)",                  `Quick, ge_plus_x_z_y ;
  "(not (= (= w x) (= y z)))",       `Quick, not_or_eq_w_x_eq_y_z ;
  "(select a k)",                    `Quick, select_a_k ;
  "(store a k v) ; empty",           `Quick, store_a_k_v__empty ;
  "(store a k v) ; non-empty",       `Quick, store_a_k_v__nonempty ;
  "(select a k)  ; with duplicates", `Quick, select_a_k__with_duplicates ;
  "(store a k v) ; with duplicates", `Quick, store_a_k_v__with_duplicates ;
  "(>= y (len x))",                  `Quick, ge_y_len_x ;
  "(all (map-fixR-int-geq l 0))",    `Quick, all_mapR_ge_l_0 ;
  "(bvadd a b)",                     `Quick, bvadd_a_b ;
  "(bvult a b)",                     `Quick, bvult_a_b ;
  "(bvnot (bvsub a b))",             `Quick, bvnot_bvsub_a_b ;
]
