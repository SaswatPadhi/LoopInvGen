open Core
open Components
open Types

let vzero = VInt 0
let vone = VInt 1

let new_components = [
  {
    name = "lia-add";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Const c1) ; (FCall ("lia-sub", [_ ; (Const c2)]))] -> c1 <> c2
             | [(FCall ("lia-sub", [_ ; (Const c1)])) ; (Const c2)] -> c1 <> c2
             | [(Const c) ; _] -> c <> vzero
             | [_ ; (Const c)] -> c <> vzero
             | [_ ; _] -> true
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VInt (x + y)
             | _ -> VError);
    dump = (fun [@warning "-8"] [a ; b] -> "(+ " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "lia-sub";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Const c) ; _] -> c <> vzero
             | [_ ; (Const c)] -> c <> vzero
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VInt (x - y)
             | _ -> VError);
    dump = (fun[@warning "-8"] [a ; b] -> "(- " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "lia-mult";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Const c) ; _] -> (c <> vzero) && (c <> vone)
             | [_ ; (Const c)] -> (c <> vzero) && (c <> vone)
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VInt (x * y)
             | _ -> VError);
    dump = (fun[@warning "-8"] [a ; b] -> "(* " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "lia-leq";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VBool (x <= y)
             | _ -> VError);
    dump = (fun[@warning "-8"] [a ; b] -> "(<= " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "lia-geq";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VBool (x >= y)
             | _ -> VError);
    dump = (fun[@warning "-8"] [a ; b] -> "(>= " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "lia-lt";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VBool (x < y)
             | _ -> VError);
    dump = (fun[@warning "-8"] [a ; b] -> "(< " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "lia-gt";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VBool (x > y)
             | _ -> VError);
    dump = (fun[@warning "-8"] [a ; b] -> "(> " ^ a ^ " " ^ b ^ ")")
  } ;
  {
    name = "lia-eq";
    codomain = TBool;
    domain = [TInt;TInt];
    check = (function
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VInt x ; VInt y] -> VBool (x = y)
             | _ -> VError);
    dump = (fun[@warning "-8"] [a ; b] -> "(= " ^ a ^ " " ^ b ^ ")")
  }
]

let all_components = Th_Bool.all_components @ new_components