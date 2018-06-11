open Core
open Components
open Types

let pos_mod x y = ((x mod y) + (abs y)) mod y

let pos_div x y = (x - (pos_mod x y)) / y

let new_components = [
  {
    name = "int-div";
    codomain = TInt;
    domain = [TInt;TInt];
    check = (function
             | [_ ; (Const c)] -> (c <> Th_LIA.vzero) && (c <> Th_LIA.vone)
             | [(Const c) ; _] -> (c <> Th_LIA.vzero) && (c <> Th_LIA.vone)
             | [x ; y] -> (x <> y)
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> if y = 0 then VError else VInt (pos_div x y)
             | _ -> VError);
    dump = (fun [@warning "-8"] [a ; b] -> "(div " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "int-mod";
    codomain = TInt;
    domain = [TInt;TInt];
    check = (function
             | [_ ; (Const c)] -> (c <> Th_LIA.vzero) && (c <> Th_LIA.vone)
             | [(Const c) ; _] -> (c <> Th_LIA.vzero) && (c <> Th_LIA.vone)
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> if y = 0 then VError else VInt (pos_mod x y)
             | _ -> VError);
    dump = (fun [@warning "-8"] [a ; b] -> "(mod " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "nonlin-int-mult";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Const c) ; _] -> (c <> Th_LIA.vzero) && (c <> Th_LIA.vone)
             | [_ ; (Const c)] -> (c <> Th_LIA.vzero) && (c <> Th_LIA.vone)
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VInt (x * y)
             | _ -> VError);
    dump = (fun [@warning "-8"] [a ; b] -> "(* " ^ a ^ " " ^ b ^ ")")
  }
]

let all_components =
  (List.filter Th_LIA.all_components ~f:(fun c -> c.name <> "lin-int-mult"))
  @ new_components
