open Core
open Components
open Types

let new_components = [
  {
    name = "nia-div";
    codomain = TInt;
    domain = [TInt;TInt];
    check = (function
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VInt (x / y)
             | _ -> VError);
    dump = List.(fun l -> "(div " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "nia-mod";
    codomain = TInt;
    domain = [TInt;TInt];
    check = (function
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VInt (x mod y)
             | _ -> VError);
    dump = List.(fun l -> "(mod " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "nia-mult";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Const c) ; _] -> (c <> Th_LIA.vzero) && (c <> Th_LIA.vone)
             | [_ ; (Const c)] -> (c <> Th_LIA.vzero) && (c <> Th_LIA.vone)
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VInt (x * y)
             | _ -> VError);
    dump = List.(fun l -> "(* " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  }
]

let all_components =
  (List.filter Th_LIA.all_components ~f:(fun c -> c.name <> "lia-mult"))
  @ new_components