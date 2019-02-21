open Base
open LoopInvGen

let y_PLUS_x () =
  let open Synthesizer in
  let result = solve {
    arg_names = [ "x" ; "y" ];
    inputs = List.map ~f:(Array.map ~f:(fun i -> Value.Int i))
               [ [| 3 ; 7 ; (-1) ; (-4) |]
               ; [| 3 ; 2 ; 13 ; 11 |] ];
    outputs = Array.map ~f:(fun i -> Value.Int i) [| 6 ; 9 ; 12 ; 7 |];
    constants = []
  } in Alcotest.(check string) "identical" "(+ x y)" result.string

let y_MINUS_z_LE_x () =
  let open Synthesizer in
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

let y_MINUS_x_MINUS_z_LE_x () =
  let open Synthesizer in
  let result = solve {
    arg_names = [ "w" ; "x" ; "y" ; "z" ];
    inputs = List.map ~f:(Array.map ~f:(fun i -> Value.Int i))
               [ [| 4 ; (-1) ; (-5) ; 1 ; (-1) ; 2 |]
               ; [| 3 ; 7 ; (-1) ; (-4) ; 1 ; 2 |]
               ; [| 9 ; (-3) ; (-10) ; 11 ; (-10) ; 2  |]
               ; [| 4 ; (-6) ; (-10) ; 11 ; (-1) ; (-3) |] ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| true ; true ; false ; false ; true ; false |];
    constants = []
  } in Alcotest.(check string) "identical" "(not (or (= w x) (= y z)))" result.string

let all = [
  "(+ x y)",              `Quick, y_PLUS_x ;
  "(>= (+ x z) y)",       `Quick, y_MINUS_z_LE_x ;
  "(not (= (= w x) (= y z)))", `Quick, y_MINUS_x_MINUS_z_LE_x ;
]
