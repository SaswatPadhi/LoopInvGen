open Core
open Components
open Types

let new_components = [
  {
    name = "lia-add";
    codomain = TInt;
    domain = [TInt; TInt];
    check = (function
             | [(Leaf "const_0") ; _] -> false
             | [_ ; (Leaf "const_0")] -> false
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
             | [(Leaf "const_0") ; _] -> false
             | [_ ; (Leaf "const_0")] -> false
             | [_ ; (Leaf a)] -> not (String.is_prefix a ~prefix:"const_-")
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
             | [(Node _) ; (Node _)] -> false
             | [(Leaf a) ; _] -> String.is_prefix a ~prefix:"const_"
                              && (a <> "const_1") && (a <> "const_0") && (a <> "const_-1")
             | [_ ; (Leaf a)] -> String.is_prefix a ~prefix:"const_"
                              && (a <> "const_1") && (a <> "const_0") && (a <> "const_-1")
             | [_ ; _] -> true
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