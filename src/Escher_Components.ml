open Batteries
open Components
open Escher_Core
open Types

let apply_component (c : component) (args : Vector.t list) =
  if (c.name = "not" && (match (snd (fst (List.hd args)))
                         with Node ("not", _) -> true | _ -> false))
  || (c.name = "mult" && (match ((snd (fst List.(hd args))), (snd (fst List.(hd (tl args)))))
                          with (Node _, Node _) -> true
                             | (Node _, Leaf a) -> not (BatString.starts_with a "const_")
                             | (Leaf a, Node _) -> not (BatString.starts_with a "const_")
                             | (Leaf a, Leaf b) -> not (BatString.((starts_with a "const_") || (starts_with b "const_")))))
  then ((("", (fun _ -> VBool false)), Node ("", [])), Array.mapi (fun _ _ -> VError) (snd (List.hd args)))
  else (
    let select i l = List.map (fun x -> x.(i)) l in
    let prs = List.map (fun (((_,x),_),_) -> x) args in
    let values = List.map snd args in
    let new_prog = fun ars -> c.apply (List.map (fun p -> p ars) prs) in
    let new_str = c.dump (List.map (fun (((x,_),_),_) -> x) args) in
    let result = Array.mapi (fun i _ -> c.apply (select i values)) (List.hd values)
    in (((new_str, new_prog), Node (c.name, List.map (fun ((_,x),_) -> x) args)), result))