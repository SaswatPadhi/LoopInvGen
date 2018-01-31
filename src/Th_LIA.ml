open Core
open Components
open Types

let vzero = VInt 0
let vone = VInt 1
let vnegone = VInt (-1)

let new_components = [
  {
    name = "lia-add";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Const c) ; _] -> c <> vzero
             | [_ ; (Const c)] -> c <> vzero
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VInt (x + y)
             | _ -> VError);
    dump = List.(fun l -> "(+ " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "lia-sub";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Const c) ; _] -> c <> vzero
             | [_ ; (Const c)] -> (match c with VInt i -> i > 0 | _ -> false)
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VInt (x - y)
             | _ -> VError);
    dump = List.(fun l -> "(- " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "lia-mult";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Const c) ; _] -> (c <> vzero) && (c <> vone) && (c <> vnegone)
             | [_ ; (Const c)] -> (c <> vzero) && (c <> vone) && (c <> vnegone)
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VInt (x * y)
             | _ -> VError);
    dump = List.(fun l -> "(* " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "lia-leq";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VBool (x <= y)
             | _ -> VError);
    dump = List.(fun l -> "(<= " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "lia-geq";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VBool (x >= y)
             | _ -> VError);
    dump = List.(fun l -> "(>= " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "lia-lt";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VBool (x < y)
             | _ -> VError);
    dump = List.(fun l -> "(< " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "lia-gt";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x; VInt y] -> VBool (x > y)
             | _ -> VError);
    dump = List.(fun l -> "(> " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "lia-eq";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x;VInt y] -> VBool (x = y)
             | _ -> VError);
    dump = List.(fun l -> "(= " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  }
]

let all_components = Th_Bool.all_components @ new_components