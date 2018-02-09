open Core
open Components
open Types

let vtrue = VBool true
let vfalse = VBool false

let new_components = [
  {
    name = "not";
    codomain = TBool;
    domain = [TBool];
    check = (function
             | [FCall ("not", _)] -> false
             | [Const _] -> false
             | [_] -> true
             | _ -> false);
    apply = (function
             | [VBool x] -> VBool (not x)
             | _ -> VError);
    dump = List.(fun l -> "(not " ^ (hd_exn l) ^ ")")
  } ;
  {
    name = "and";
    codomain = TBool;
    domain = [TBool;TBool];
    check = (function
             | [(Const a) ; _] -> false
             | [_ ; (Const a)] -> false
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VBool x ; VBool y] -> VBool (x && y)
             | _ -> VError);
    dump = List.(fun l -> "(and " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  } ;
  {
    name = "or";
    codomain = TBool;
    domain = [TBool;TBool];
    check = (function
             | [(Const a) ; _] -> false
             | [_ ; (Const a)] -> false
             | [x ; y] -> x <> y
             | _ -> false);
    apply = (function
             | [VBool x ; VBool y] -> VBool (x || y)
             | _ -> VError);
    dump = List.(fun l -> "(or " ^ (hd_exn l) ^ " " ^ (hd_exn (tl_exn l)) ^ ")")
  }
]

let all_components = new_components