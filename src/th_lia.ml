open Components
open Types

let components = [
  {
    name = "+";
    codomain = TInt;
    domain = [TInt; TInt];
    apply = (function
             | [VInt x; VInt y] -> VInt (x + y)
             | _ -> VError);
    dump = (fun l -> "(+ " ^ (List.hd l) ^ " " ^ List.(hd (tl l)) ^ ")")
  } ;
  {
    name = "-";
    codomain = TInt;
    domain = [TInt; TInt];
    apply = (function
             | [VInt x; VInt y] -> VInt (x - y)
             | _ -> VError);
    dump = (fun l -> "(- " ^ (List.hd l) ^ " " ^ List.(hd (tl l)) ^ ")")
  } ;
  {
    name = "*";
    codomain = TInt;
    domain = [TInt; TInt];
    apply = (function
             | [VInt x; VInt y] -> VInt (x * y)
             | _ -> VError);
    dump = (fun l -> "(* " ^ (List.hd l) ^ " " ^ List.(hd (tl l)) ^ ")")
  } ;
  {
    name = "<=";
    codomain = TBool;
    domain = [TInt;TInt];
    apply = (function
             | [VInt x; VInt y] -> VBool (x <= y)
             | _ -> VError);
    dump = (fun l -> "(<= " ^ (List.hd l) ^ " " ^ List.(hd (tl l)) ^ ")")
  } ;
  {
    name = ">=";
    codomain = TBool;
    domain = [TInt;TInt];
    apply = (function
             | [VInt x; VInt y] -> VBool (x >= y)
             | _ -> VError);
    dump = (fun l -> "(>= " ^ (List.hd l) ^ " " ^ List.(hd (tl l)) ^ ")")
  } ;
  {
    name = "<";
    codomain = TBool;
    domain = [TInt;TInt];
    apply = (function
             | [VInt x; VInt y] -> VBool (x < y)
             | _ -> VError);
    dump = (fun l -> "(< " ^ (List.hd l) ^ " " ^ List.(hd (tl l)) ^ ")")
  } ;
  {
    name = ">";
    codomain = TBool;
    domain = [TInt;TInt];
    apply = (function
             | [VInt x; VInt y] -> VBool (x > y)
             | _ -> VError);
    dump = (fun l -> "(> " ^ (List.hd l) ^ " " ^ List.(hd (tl l)) ^ ")")
  } ;
  {
    name = "=";
    codomain = TBool;
    domain = [TInt;TInt];
    apply = (function
             | [VInt x;VInt y] -> VBool (x = y)
             | _ -> VError);
    dump = (fun l -> "(= " ^ (List.hd l) ^ " " ^ List.(hd (tl l)) ^ ")")
  }
]