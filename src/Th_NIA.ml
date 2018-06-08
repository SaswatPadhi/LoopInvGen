open Core
open Components
open Types


let new_components = [
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
             | [VInt x ; VInt y] -> VInt (x * y)
             | _ -> VError);
    dump = (fun [@warning "-8"] [a ; b] -> "(* " ^ a ^ " " ^ b ^ ")")
  }
]

let all_components =
  (List.filter Th_LIA.all_components ~f:(fun c -> c.name <> "lia-mult"))
  @ new_components
