open Base

open Type

(* Unification algorithm referenced from http://www.cs.cornell.edu/courses/cs3110/2011fa/supplemental/lec26-type-inference/type-inference.htm *)
type substitution = (string * Type.t) list 

exception UnifyError of string

let collect_varname t = 
  let rec collect t acc = match t with 
  | TVAR i -> i :: acc 
  | LIST t1 -> collect t1 acc
  | _ -> acc in 
  collect t []

let collect_varnames t = 
  let l = List.map ~f:collect_varname t in
  let l = List.concat l in
  List.dedup_and_sort ~compare:String.compare l

let rename names terms = 
  let table = Hashtbl.create (module String) in 
  List.iter names ~f:(fun name -> Hashtbl.set table ~key:name ~data:());
  let rec fresh s suffix = 
    let name = s ^ Int.to_string suffix in
    match Hashtbl.mem table name with 
    | true -> fresh s (suffix + 1)
    | false -> name in 
  let rec do_rename t = match t with 
    | TVAR s -> TVAR (fresh s 0)
    | LIST t1 -> LIST (do_rename t1)
    | _ -> t in 
  List.map ~f:do_rename terms

let rec occurs svar t = match t with 
  | TVAR s -> String.equal svar s
  | LIST t1 -> occurs svar t1
  | _ -> false

let rec subst (id,sub) t = match t with 
  | TVAR x -> if String.equal x id then sub else t
  | LIST t1 -> LIST (subst (id,sub) t1)
  | _ -> t

let apply subs typ = 
  List.fold_right ~f:(fun s t -> subst s t) ~init:typ subs

let rec unify_one (t1 : Type.t) (t2 : Type.t) : substitution = match (t1, t2) with 
  | TVAR x, TVAR y -> if String.equal x y then [] else [(x, t2)]
  | TVAR x, t2 -> if occurs x t2 then raise (UnifyError "cannot unify: circularity") else [(x, t2)]
  | t1, TVAR x -> if occurs x t1 then raise (UnifyError "cannot unify: circularity") else [(x, t1)]
  | LIST x, LIST y -> unify_one x y 
  | INT, INT | BOOL, BOOL -> []
  | _ -> raise (UnifyError "cannot unify: different types")

let rec unify (t1 : Type.t list) (t2 : Type.t list) : substitution = match (t1, t2) with 
  | (x :: tx, y :: ty) -> 
    let s2 = unify tx ty in
    let s1 = unify_one (apply s2 x) (apply s2 y) in begin 
      match s1 with [el] -> el :: s2 | _ -> s2
    end
  | _ -> []

let unifiable t1 t2 = try ignore (unify t1 t2); true with _ -> false