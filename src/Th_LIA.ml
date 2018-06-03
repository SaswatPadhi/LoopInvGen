open Core
open Components
open Types

let vzero = VInt 0
let vone = VInt 1

let new_components = [
  {
    name = "int-add";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [x ; (FCall ("int-sub", [_ ; y]))] -> x <> y
             | [(FCall ("int-sub", [_ ; x])) ; y] -> x <> y
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
    name = "int-sub";
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
    name = "lin-int-mult";
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
    name = "int-leq";
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
    name = "int-geq";
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
    name = "int-lt";
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
    name = "int-gt";
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
    name = "int-eq";
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