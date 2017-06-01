open BFL
open CNF
open Core
open Exceptions
open Utils
open ZProc

type note
type 'a feature = 'a -> bool
type 'a with_note = 'a * note
type ('a, 'b) postcond = 'a -> ('b, exn) Result.t -> bool

type ('a, 'b) job = {
  f : 'a -> 'b ;
  post : ('a, 'b) postcond ;
  features : 'a feature with_note list ;
  pos_tests : ('a * (bool list lazy_t)) list ;
  neg_tests : ('a * (bool list lazy_t)) list ;
}

let create_job ~f ~post ~features ~tests =
  let (pos, neg) = List.fold ~init:([],[]) tests
    ~f:(fun (l1,l2) t -> try if post t (Result.try_with (fun () -> f t))
                             then (t :: l1, l2) else (l1, t :: l2)
                         with IgnoreTest -> (t :: l1, l2)
                            | _ -> (l1, t :: l2))
  in let compute_fvec t =
       List.map features ~f:(fun (f, _) -> try f t with _ -> false)
  in { f ; post ; features
     ; pos_tests = List.map pos ~f:(fun t -> (t, lazy (compute_fvec t)))
     ; neg_tests = List.map neg ~f:(fun t -> (t, lazy (compute_fvec t)))
     }

(* k is the maximum clause length for the formula we will provide (i.e., it's
   a k-cnf formula) f is the function whose spec we are inferring tests is a
   set of inputs on which to test f features is a set of predicates on inputs
   that we use as features for our learning.

   If the flag strengthen is true, we attempt to find a formula that falsifies
   all negative examples and satisfies at least one positive example but might
   falsify others. This is useful if we are trying to find a simple
   strengthening of the "actual" precondition.

   costs is an optional mapping from the nth feature (numbered 1 through n
   according to their order) to a cost (float) - lower is better.
   
   post is the postcondition whose corresponding precondition formula we are
   trying to learn we associate some kind of description (of polymorphic type
   'c) with each feature and postcondition. *)
let learnPreCond ?(k = 3) ?(strengthen = false) ?(autoIncrK = false)
                 (job : ('a, 'b) job) : ('a feature with_note) CNF.t option =
  let make_f_vecs = List.map ~f:(fun (_, fvec) -> Lazy.force fvec) in
  let (pos_vecs, neg_vecs) = List.(dedup (make_f_vecs job.pos_tests),
                                   dedup (make_f_vecs job.neg_tests)) in
  let rec learnWithK k =
    try let cnf = learnKCNF ~k ~strengthen ~n:(List.length job.features)
                            pos_vecs neg_vecs
        in Some (CNF.map cnf ~f:(fun i -> List.nth_exn job.features (i - 1)))
    with NoSuchFunction -> if autoIncrK then learnWithK (k + 1) else None
       | ClauseEncodingError -> None
  in learnWithK k

(* this function takes the same arguments as does learnSpec and returns groups
   of tests that illustrate a missing feature. Each group has the property that
   all inputs in the group lead to the same truth assignment of features, but
   the group contains at least one positive and one negative example (in terms
   of the truth value of the given postcondition). Hence the user needs to
   provide a new feature that can separate these examples. *)
let missingFeature (job : ('a, 'b) job) : (('a list) * (bool list)) list =
  let make_f_vecs = List.map ~f:(fun (t, fvec) -> (t, Lazy.force fvec)) in
  let make_groups tests =
    List.(filter (group tests ~break:(fun (_, fv1) (_, fv2) -> fv1 <> fv2))
                 ~f:(fun l -> length l > 1)) in
  let (p_groups, n_groups) = (make_groups (make_f_vecs job.pos_tests),
                              make_groups (make_f_vecs job.neg_tests))
  (* find feature vectors that are in pos_groups and neg_groups *)
  in List.(filter_map
       p_groups
       ~f:(fun (((_, pfv) :: _) as ptests) ->
             match find n_groups ~f:(fun ((_, nfv) :: _) -> nfv = pfv) with
             | None -> None
             | Some ntests -> Some (map (ptests @ ntests) ~f:fst, pfv)))