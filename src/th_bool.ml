open Components
open Types

let components = [
  {
    name = "not";
    codomain = TBool;
    domain = [TBool];
    apply = (function
             | [VBool x] -> VBool (not x)
             | _ -> VError);
    dump = (fun l -> "(! " ^ (List.hd l) ^ ")")
  } ;
  {
    name = "and";
    codomain = TBool;
    domain = [TBool;TBool];
    apply = (function
             | [VBool x; VBool y] -> VBool (x && y)
             | _ -> VError);
    dump = (fun l -> "(and " ^ (List.hd l) ^ " " ^ (List.hd (List.tl l)) ^ ")")
  } ;
  {
    name = "or";
    codomain = TBool;
    domain = [TBool;TBool];
    apply = (function
             | [VBool x; VBool y] -> VBool (x || y)
             | _ -> VError);
    dump = (fun l -> "(or " ^ (List.hd l) ^ " " ^ (List.hd (List.tl l)) ^ ")")
  }
]