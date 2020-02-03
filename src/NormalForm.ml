open Core
open Sexp

let flatten ~op ~default args =
  let branches = List.concat_map args ~f:(function List (Atom o :: b)
                                                   when String.equal o op -> b
                                                 | b -> [b])
   in match branches with
      | [] -> Atom default
      | [b] -> b
      | _ -> List (Atom op :: branches)

let flatten_or = flatten ~op:"or" ~default:"false"

let flatten_and = flatten ~op:"and" ~default:"true"

let de_morgan_simplify = function
  | List [Atom "not" ; List (Atom "and" :: args)]
    -> List (Atom "or" :: List.map args ~f:(fun e -> List [Atom "not" ; e]))
  | List [Atom "not" ; List (Atom "or" :: args)]
    -> List (Atom "and" :: List.map args ~f:(fun e -> List [Atom "not" ; e]))
  | f -> f

let rec to_nnf f = match f with
  | List [Atom "not" ; List (Atom "and" :: _)]
    -> to_nnf (de_morgan_simplify f)
  | List [Atom "not" ; List (Atom "or" :: _)]
    -> to_nnf (de_morgan_simplify f)
  | List [Atom "not" ; List [Atom "not" ; f_inner]]
    -> to_nnf f_inner
  | List (Atom "and" :: args)
    -> flatten_and (List.map args ~f:to_nnf)
  | List (Atom "or" :: args)
    -> flatten_or (List.map args ~f:to_nnf)
  | _ -> f

let rec nnf_to_rulenf rule nnf =
  let partial_rulenf = match nnf with
    | Atom _ | List [Atom "not" ; _] -> nnf
    | List (Atom "and" :: args)
      -> flatten_and (List.map args ~f:(nnf_to_rulenf rule))
    | List (Atom "or" :: args)
      -> flatten_or (List.map args ~f:(nnf_to_rulenf rule))
    | List l
      -> List (List.map l ~f:(nnf_to_rulenf rule))
  in rule partial_rulenf

let dnf_rule nnf = match nnf with
  | List (Atom "or" :: args) -> flatten_or args
  | List (Atom "and" :: args)
    -> let or_branches, and_branches = List.(
           filter_map args ~f:(function List (Atom "or" :: b) -> Some b
                                      | _ -> None),
           concat_map args ~f:(function List (Atom "or" :: _) -> []
                                      | List (Atom "and" :: b) -> b
                                      | a -> [a])
       ) in begin match or_branches with
              | [] -> flatten_and and_branches
              | first_or :: rest_ors
                -> let branches = List.(
                     map ~f:(fun (l,e) -> flatten_and (e :: l))
                         (fold rest_ors
                               ~init:(cartesian_product [and_branches] first_or)
                               ~f:(fun acc -> let merged = map acc ~f:(fun (l,e) -> e :: l)
                                               in cartesian_product merged)))
                    in flatten_or branches
            end
  | _ -> nnf

let nnf_to_dnf = nnf_to_rulenf dnf_rule

let to_dnf f = nnf_to_dnf (to_nnf f)