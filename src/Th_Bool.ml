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
    dump = (fun [@warning "-8"] [a] -> "(not " ^ a ^ ")")
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
    dump = (fun [@warning "-8"] [a ; b] -> "(and " ^ a ^ " " ^ b ^ ")")
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
    dump = (fun [@warning "-8"] [a ; b] -> "(or " ^ a ^ " " ^ b ^ ")")
  }
]

let all_components = new_components