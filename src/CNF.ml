open Utils

(* a type for cnf formulas, parameterized by the type used for literals *)
type 'a literal = Pos of 'a | Neg of 'a
type 'a clause = 'a literal list
type 'a t = 'a clause list

let map ~(f : 'a -> 'b) (cnf : 'a t) : 'b t =
  List.map cnf ~f:(fun clause ->
                     List.map clause ~f:(function
                                         | Pos a -> Pos (f a)
                                         | Neg a -> Neg (f a)))

let literal_to_string ?(human = false) ~(stringify : 'a -> string)
                      (literal : 'a literal) : string =
  match literal with
  | Pos x -> stringify x
  | Neg x -> if human then "(~" ^ (stringify x) ^ ")"
                      else "(not " ^ (stringify x) ^ ")"

let clause_to_string ?(fsym = "false") ?(human = false) (clause : 'a clause)
                     ~(stringify : 'a -> string) : string =
  let literal_to_string = literal_to_string ~human ~stringify in
  match clause with
  | [] -> fsym
  | h::t -> if human
            then List.to_string_map clause ~sep:" \\/ " ~f:literal_to_string
            else List.(fold t ~init:(literal_to_string h)
                            ~f:(fun s l -> "(or " ^ s ^ " " ^
                                           (literal_to_string l) ^ ")"))

let to_string ?(tsym = "true") ?(fsym = "false") ?(human = false) (cnf : 'a t)
              ~(stringify : 'a -> string) : string =
  let clause_to_string = clause_to_string ~fsym ~human ~stringify in
  match cnf with
  | [] -> tsym
  | [[]] -> fsym
  | h::t -> if human
            then List.to_string_map cnf ~sep:" /\\ " ~f:clause_to_string
            else List.(fold t ~init:(clause_to_string h)
                            ~f:(fun s c -> "(and " ^ s ^ " " ^
                                           (clause_to_string c) ^ ")"))