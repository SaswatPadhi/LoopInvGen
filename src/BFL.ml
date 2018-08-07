open Base

open CNF
open Exceptions
open Utils

type conjunct = int list

type truthAssignment = (int, bool) Hashtbl.t

type config = {
  auto_incr_k : bool ;
  k : int ;
  strengthen : bool ;
}

let default_config = {
  auto_incr_k = true ;
  k = 1 ;
  strengthen = false ;
}

let truthAssignment_to_string (ta : truthAssignment) : string =
  "[" ^ (Hashtbl.fold ta ~init:""
                      ~f:(fun ~key ~data s -> s ^ "(" ^ (Int.to_string key) ^ ","
                                            ^ (Bool.to_string data) ^ ") ; "))
 ^ "]"

(* remove literals from conj that are inconsistent with the given example *)
let pruneWithAPositiveExample (conj : conjunct) (example : truthAssignment)
                              : conjunct =
  List.filter conj ~f:(fun v -> Hashtbl.find_default example v ~default:true)

(* use a greedy heuristic to identify a set of literals in conj
   that cover all of the negative examples in example
   (i.e., that conjunction of literals suffices to falsify all
   of the provided negative examples). *)
let pruneWithNegativeExamples (conj : conjunct)
                              (example : truthAssignment list) : conjunct =
  let find_or_true = Hashtbl.find_default ~default:true in
  let rec helper conj remaining accum =
    if List.equal ~equal:Poly.equal remaining [] then accum
    else if List.equal ~equal:Int.equal conj [] then raise NoSuchFunction
    else begin
      (* for each variable in conj, count the negative examples it covers
        (i.e, on how many of the examples it has the truth value false) *)
      let counts = List.map conj
        ~f:(fun v -> (v, List.count remaining
                                    ~f:(fun ex -> not (find_or_true ex v)))) in

      (* find the variable with the largest number of covered examples *)
      let (cVar, cCnt) = Option.value_exn (
        List.max_elt counts ~compare:(fun vn1 vn2 -> compare (snd vn1) (snd vn2))
      ) in
      (* if no literals cover any of the remaining negative examples, then
         there is no boolean function that properly classifies all of the
         original positive and negative examples *)
      if cCnt = 0 then raise NoSuchFunction else
      begin
        (* keep the chosen variable and recurse:
           filtering out this variable from the conjunction,
           and filtering out the negative examples that it covers.

           We also filter out the negated version of the chosen variable.
           This is necessary when we are using this function to find missing
           tests, so we don't say that (X and (not X)) is a missing test.
           When this function is used as part of learning a conjunction,
           there will be no negative variables
           (see the comment on learnConjunction about not including
           negative literals), so it will be a no-op in that case. *)
        helper (List.filter conj ~f:(fun v -> v <> cVar))
               (List.filter remaining ~f:(fun ex -> find_or_true ex cVar))
               (cVar :: accum)
      end
    end
  in helper conj example []

(* learn a simple conjunction that falsifies all negative examples
   but may not satisfy all positive examples *)
let learnStrongConjunction (conj : conjunct) (pos : truthAssignment list)
                           (neg : truthAssignment list) : conjunct =
  let find_or_true = Hashtbl.find_default ~default:true in
  let rec helper conj remainingNeg accum =
    if List.equal ~equal:Poly.equal remainingNeg [] then accum
    else if List.equal ~equal:Int.equal conj [] then raise NoSuchFunction
    else begin
      (* for each variable in conj, count the negative examples it covers
         (i.e, on how many of the examples it has the truth value false) *)
      let counts = List.map conj
        ~f:(fun v -> (v, List.count remainingNeg
                                    ~f:(fun ex -> not (find_or_true ex v)))) in

      (* find the variable with the largest number of covered examples *)
      let (cVar, cCnt) = Option.value_exn (
        List.max_elt counts ~compare:(fun vn1 vn2 -> compare (snd vn1) (snd vn2))
      ) in
      (* if no literals cover any of the remaining negative examples, then
         there is no boolean function that properly classifies all of the
         original positive and negative examples *)
      if cCnt = 0 then raise NoSuchFunction else
      begin
        (* keep the chosen variable and recurse:
           filtering out this variable from the conjunction,
           and filtering out the negative examples that it covers. *)
        let accum' = cVar :: accum in
        let helper' = helper (List.filter conj ~f:(fun v -> v <> cVar)) in

        if List.for_all pos
             ~f:(fun ex -> List.exists accum'
                                       ~f:(fun i -> not (find_or_true ex i)))
        (* if the addition of cVar makes it so our result will not satisfy any
           positive tests, then we throw out that cVar and keep looking *)
        then helper' remainingNeg accum
        else helper' (List.filter remainingNeg
                                  ~f:(fun ex -> find_or_true ex cVar))
                     accum'
      end
    end
  in helper conj neg []

(* learn an unknown conjunct over the variables in list vars using the given set
   of positive and negative examples (list of truth assignments for which the
   unknown conjunct evaluates to true and false respectively).

   in the normal algorithm, you start with an initial conjunction of the form

     x1 and (not x1) and x2 and (not x2) and ... xn and (not xn)

   where the variables are x1...xn

   here we omit the negated ones because they are superfluous given our
   encoding of all possible disjuncts on the original variables as variables
   here (see the 3CNF learning algorithm below).

   so this is not a general algorithm for learning conjunctions

   if the flag strengthen is true, we attempt to find a conjunct that falsifies
   all negative examples and satisfies at least one positive example but might
   falsify others.  this is useful if we are trying to find a simple
   strengthening of the "true" precondition.

   costs is a map from variables to an integer cost, which is used as
   part of the greedy heuristic for learning from negative examples. *)
let learnConjunction ?(strengthen = false) (vars : conjunct)
                     (pos : truthAssignment list) (neg : truthAssignment list)
                     : conjunct =
  (* the initial conjunction is the AND of all variables *)
  let conj = vars in
  if strengthen then learnStrongConjunction conj pos neg
  else let conj = List.fold pos ~init:conj ~f:pruneWithAPositiveExample
       in pruneWithNegativeExamples conj neg

(* produce all k-tuples (considered as sets) of numbers from 1 to n *)
let allKTuples (k : int) (n : int) : conjunct list =
  let srange = List.range ~stop:`inclusive in
  let rec aux k l rest =
    begin match k with
     | 1 -> rest @ l
     | _ -> let next = List.(
              concat_map l ~f:(fun l ->
                                 match l with
                                 | [] -> []
                                 | x :: _
                                   -> map (srange (x+1) n) ~f:(fun v -> v::l))
              ) in aux (k - 1) next (rest @ l)
    end in
  let tuples = aux k (List.map (srange 1 n) ~f:(fun x -> [x])) [[]] in
    (* include all k-tuples with negative literals as well *)
    List.(concat_map tuples
                     ~f:(fun t -> fold t ~init:[[]]
                                       ~f:(fun c x ->
                                             let x' = x + n
                                             in (map c ~f:(fun l -> x::l))
                                              @ (map c ~f:(fun l -> x'::l)))))

(* Given n variables over a k-CNF formula to learn, we create one variable
   per possible k-clause to use in the reduction to conjunction learning *)
let cnfVarsToClauseVars k n : (int * conjunct) list =
  (* We use bit-packing to represent a clause (a set of ints) as a single int.
     Our current encoding uses 10 bits per int and so requires:
      - 64-bit architecture
      - k <= 6
      - n*2 < 2^10 *)
  if Sys.word_size_in_bits <> 64 || k > 6 || n > 500 then raise ClauseEncodingError
  else List.(map (allKTuples k n)
                 ~f:(fun t -> let (enc, _) = fold t ~init:(0,0)
                                  ~f:(fun (enc,b) x -> (enc lor (x lsl b), b+10))
                        in (enc, t)))

(* PAC-learn a k-CNF formula over the variables numbered 1 to n, given a set of
   positive and negative examples (list of truth assignments, each represented
   as a list of bools over n variables.)

   If the flag strengthen is true, we attempt to find a formula that falsifies
   all negative examples and satisfies at least one positive example but might
   falsify others.  this is useful if we are trying to find a simple
   strengthening of the "true" precondition. *)
let learnCNF ?(conf = default_config) ~(n : int) (pos : bool list list)
             (neg : bool list list) : int CNF.t =
  let rec helper k =
  begin
    Log.debug (lazy ("Attempting BFL with K = " ^ (Int.to_string k))) ;
    (* create one variable per possible k-clause over the given variables *)
    let varEncoding = cnfVarsToClauseVars k n in
    let augmentExamples =
          List.(map ~f:(foldi ~init:[]
                              ~f:(fun i curr b -> (i+1, b) :: (i + n + 1, not b)
                                                           :: curr)))
    (* translate an example on the original variables
      to one on the new variables *)
    in let encodeExamples ex =
         let ex = Hashtbl.Poly.of_alist_exn ex in Hashtbl.Poly.of_alist_exn (
                    List.map varEncoding
                             ~f:(fun (i, c) ->
                                   (i, List.exists c ~f:(Hashtbl.find_exn ex))))
    in let pos = List.map ~f:encodeExamples (augmentExamples pos)
    in let neg = List.map ~f:encodeExamples (augmentExamples neg)
    (* learn a conjunction on the new variables *)
    in let vars = List.map ~f:fst varEncoding
    in try
         let learnedConjunct = learnConjunction vars pos neg
                                                ~strengthen:conf.strengthen
         in let decodeClause i =
              let rec aux n = match (i lsr n) land 0x3ff with
                              | 0 -> []
                              | lit -> lit :: (aux (n + 10))
              in aux 0
         in let learnedkCNF = List.map ~f:decodeClause learnedConjunct in
         (* convert the result into cnf type *)
         let indexToLit i = if i <= n then Pos i else Neg (i - n)
         in List.map ~f:(List.map ~f:indexToLit) learnedkCNF
       with NoSuchFunction
            -> if not conf.auto_incr_k then raise NoSuchFunction
                                       else helper (k + 1)
  end in helper conf.k