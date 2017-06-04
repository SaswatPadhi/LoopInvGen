open BFL
open CNF
open Core
open Exceptions
open Types
open Utils

type desc = string
type 'a feature = 'a -> bool
type 'a with_desc = 'a * desc
type ('a, 'b) postcond = 'a -> ('b, exn) Result.t -> bool

type 'a conflict = {
  pos : 'a list ;
  neg : 'a list ;
  fvec : bool list ;
}

type ('a, 'b) job = {
  f : 'a -> 'b ;
  farg_names : string list ;
  farg_types : Types.typ list ;
  features : 'a feature with_desc list ;
  neg_tests : ('a * (bool list lazy_t)) list ;
  pos_tests : ('a * (bool list lazy_t)) list ;
  post : ('a, 'b) postcond ;
}

let split_tests tests ~f ~post =
  List.fold ~init:([],[]) tests
    ~f:(fun (l1,l2) t -> try if post t (Result.try_with (fun () -> f t))
                             then (t :: l1, l2) else (l1, t :: l2)
                         with IgnoreTest -> (l1, l2)
                            | _ -> (l1, t :: l2))

let compute_feature_vector features test =
  List.map features ~f:(fun (f, _) -> try f test with _ -> false)

(* Creates a new job with appropriate lazy computations.
   Our jobs deal with Types.value to enable feature synthesis with Escher. *)
let create_pos_job ~f ~args ~post ?(features = []) ~pos_tests ()
                   : (value list, value) job =
  let compute_fvec = compute_feature_vector features
  in { f ; post ; features
     ; farg_names = List.map args ~f:fst
     ; farg_types = List.map args ~f:snd
     ; pos_tests = List.map pos_tests ~f:(fun t -> (t, lazy (compute_fvec t)))
     ; neg_tests = []
     }

(* Creates a new job with appropriate lazy computations.
   Our jobs deal with Types.value to enable feature synthesis with Escher. *)
let create_job ~f ~args ~post ?(features = []) ~tests ()
               : (value list, value) job =
  let (pos, neg) = split_tests (List.dedup tests) ~f ~post
  in let compute_fvec = compute_feature_vector features
  in { (create_pos_job () ~f ~args ~post ~features ~pos_tests:pos) with
         neg_tests = List.map neg ~f:(fun t -> (t, lazy (compute_fvec t)))
     }

let add_tests ~(job : ('a, 'b) job) (tests : 'a list) : (('a, 'b) job * int) =
  let (pos, neg) = split_tests (List.dedup tests) ~f:job.f ~post:job.post
  in let pos = List.(filter pos ~f:(fun t -> not (exists job.pos_tests
                                                    ~f:(fun (p, _) -> p = t))))
  in let neg = List.(filter neg ~f:(fun t -> not (exists job.neg_tests
                                                    ~f:(fun (n, _) -> n = t))))
  in let compute_fvec = compute_feature_vector job.features
  in ({ job with
         pos_tests = List.map pos ~f:(fun t -> (t, lazy (compute_fvec t)))
                   @ job.pos_tests ;
         neg_tests = List.map neg ~f:(fun t -> (t, lazy (compute_fvec t)))
                   @ job.neg_tests ;
      },
      List.(length pos + length neg))

let add_features ~(job : ('a, 'b) job) (features : 'a feature with_desc list)
                 : ('a, 'b) job =
  let add_to_fvec fs (t, fv) =
    (t, lazy ((compute_feature_vector fs t) @ (Lazy.force fv)))
  in { job with
         features = features @ job.features ;
         pos_tests = List.map job.pos_tests ~f:(add_to_fvec features) ;
         neg_tests = List.map job.neg_tests ~f:(add_to_fvec features) ;
     }

(* this function takes the same arguments as does learnSpec and returns groups
   of tests that illustrate a missing feature. Each group has the property that
   all inputs in the group lead to the same truth assignment of features, but
   the group contains at least one positive and one negative example (in terms
   of the truth value of the given postcondition). Hence the user needs to
   provide new features that can separate these examples. *)
let conflictingTests (job : ('a, 'b) job) : 'a conflict list =
  let make_f_vecs = List.map ~f:(fun (t, fvec) -> (t, Lazy.force fvec)) in
  let make_groups tests =
    List.group tests ~break:(fun (_, fv1) (_, fv2) -> fv1 <> fv2)
  in let (p_groups, n_groups) = (make_groups (make_f_vecs job.pos_tests),
                                 make_groups (make_f_vecs job.neg_tests))
  (* find feature vectors that are in pos_groups and neg_groups *)
  in List.(filter_map
       p_groups
       ~f:(fun (((_, pfv) :: _) as ptests) ->
             match find n_groups ~f:(fun ((_, nfv) :: _) -> nfv = pfv) with
             | None -> None
             | Some ntests -> Some { pos = map ~f:fst ptests
                                   ; neg = map ~f:fst ntests
                                   ; fvec = pfv }))

(* Synthesize a new feature to resolve a conflict group. *)
let synthFeatures ?(consts = []) ~(job : (value list, value) job)
                  (c_group : value list conflict)
                  : value list feature with_desc list =
  let group_size = List.((length c_group.pos) + (length c_group.neg))
  in let tab = Hashtbl.Poly.create () ~size:group_size
  in List.iter c_group.pos ~f:(fun v -> Hashtbl.add_exn tab ~key:v ~data:vtrue)
   ; List.iter c_group.neg ~f:(fun v -> Hashtbl.add_exn tab ~key:v ~data:vfalse)
   ; let open Components in
     let open Escher_Core in
     let open Escher_Synth in
     let f_synth_task = {
       target = {
         domain = job.farg_types;
         codomain = TBool;
         apply = (Hashtbl.find_default tab ~default:VDontCare);
         name = "synth";
         dump = _unsupported_
       };
       inputs = List.mapi job.farg_names ~f:(fun i n ->
          (((n, (fun ars -> List.nth_exn ars i)), Leaf n),
           let ith_args = Array.create ~len:group_size VDontCare
           in (List.iteri (Hashtbl.keys tab)
                          ~f:(fun j args ->
                                ith_args.(j) <- (List.nth_exn args i)))
              ; ith_args));
       components = default_components
     }
  in let solutions = solve f_synth_task consts
  in List.map solutions ~f:(fun (desc, f) -> (fun v -> (f v) = vtrue), desc)

let resolveSingleConflict ?(consts = []) ~(job : (value list, value) job)
                          ?(max_c_group_size = 24)
                          (c_group' : value list conflict)
                          : value list feature with_desc list =
  let group_size = List.((length c_group'.pos) + (length c_group'.neg))
  in let c_group = if group_size < max_c_group_size then c_group'
                   else {
                     c_group' with
                       pos = List.take c_group'.pos (max_c_group_size / 2) ;
                       neg = List.take c_group'.neg (max_c_group_size / 2)
                   }
  in let new_features = synthFeatures ~consts ~job c_group
  in Log.debug (lazy ("Synthesized features:" ^ Log.indented_sep ^
                      (List.to_string_map new_features
                         ~sep:Log.indented_sep ~f:snd)))
   ; new_features

let rec resolveConflicts ?(consts = []) ~(job : (value list, value) job)
                         ?(max_c_group_size = 24)
                         (c_groups : value list conflict list)
                         : value list feature with_desc list =
  if c_groups = [] then []
  else let new_features = resolveSingleConflict ~consts ~job ~max_c_group_size
                                                (List.hd_exn c_groups)
       in if not (new_features = []) then new_features
          else resolveConflicts ~consts ~job ~max_c_group_size
                                (List.tl_exn c_groups)

let rec augmentFeatures ?(consts = []) ?(max_c_group_size = 24)
                        ?(disable_synth = false) (job : (value list, value) job)
                        : (value list, value) job option =
  let c_groups = conflictingTests job
  in if c_groups = [] then Some job
     else if disable_synth then None
     else let new_features = resolveConflicts c_groups ~consts ~job
                                              ~max_c_group_size
          in if new_features = []
             then (Log.debug (lazy ("CONFLICT RESOLUTION FAILED")) ; None)
             else augmentFeatures ~consts (add_features ~job new_features)

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
let learnPreCond ?(strengthen = false) ?(k = 1) ?(auto_incr_k = true)
                 ?(consts = []) ?(max_c_group_size = 24)
                 ?(disable_synth = false) (job : ('a, 'b) job)
                 : ('a feature with_desc) CNF.t option =
  Log.debug (lazy ("Learning with "
                  ^ (string_of_int (List.length job.pos_tests))
                  ^ " POS + "
                  ^ (string_of_int (List.length job.neg_tests))
                  ^ " NEG tests")) ;
  match augmentFeatures ~consts ~max_c_group_size ~disable_synth job with
  | None -> None
  | Some job -> begin
      let make_f_vecs = List.map ~f:(fun (_, fvec) -> Lazy.force fvec) in
      let (pos_vecs, neg_vecs) = List.(dedup (make_f_vecs job.pos_tests),
                                      dedup (make_f_vecs job.neg_tests)) in
      let rec learnWithK k =
        Log.debug (lazy ("Attempting with K = " ^ (string_of_int k))) ;
        try let cnf = learnKCNF ~k ~strengthen ~n:(List.length job.features)
                                pos_vecs neg_vecs
            in Some (CNF.map cnf ~f:(fun i -> List.nth_exn job.features (i-1)))
        with NoSuchFunction -> if auto_incr_k then learnWithK (k + 1) else None
          | ClauseEncodingError -> None
      in learnWithK k
    end

let cnf_opt_to_desc (pred : ('a feature with_desc) CNF.t option) : desc =
  match pred with
  | None -> "false"
  | Some pred -> CNF.to_string pred ~stringify:snd