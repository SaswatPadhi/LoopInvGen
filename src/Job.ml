open Core_kernel

open Exceptions
open Utils

type desc = string
type 'a feature = 'a -> bool
type 'a with_desc = 'a * desc
type ('a, 'b) postcond = 'a -> ('b, exn) Result.t -> bool

type ('a, 'b) _t = {
  f : 'a -> 'b ;
  farg_names : string list ;
  farg_types : Type.t list ;
  features : 'a feature with_desc list ;
  neg_tests : ('a * (bool list lazy_t)) list ;
  pos_tests : ('a * (bool list lazy_t)) list ;
  post : ('a, 'b) postcond ;
}

type t = (Value.t list, Value.t) _t

let compute_feature_value (test : 'a) (feature : 'a feature with_desc) : bool =
  try (fst feature) test with _ -> false
  [@@inline always]

let compute_feature_vector (test : 'a) (features : 'a feature with_desc list)
                           : bool list =
  List.map ~f:(compute_feature_value test) features
  [@@inline always]

let create_positive ~f ~args ~post ?(features = []) pos_tests : t =
  { f ; post ; features
  ; farg_names = List.map args ~f:fst
  ; farg_types = List.map args ~f:snd
  ; pos_tests = List.map pos_tests ~f:(fun t -> (t, lazy (compute_feature_vector t features)))
  ; neg_tests = []
  }

let split_tests ~f ~post tests =
  List.fold ~init:([],[]) tests
    ~f:(fun (l1,l2) t -> try if post t (Result.try_with (fun () -> f t))
                             then (t :: l1, l2) else (l1, t :: l2)
                         with IgnoreTest -> (l1, l2)
                            | _ -> (l1, t :: l2))

let create ~f ~args ~post ?(features = []) tests : t =
  let (pos, neg) = split_tests (List.dedup_and_sort ~compare:(List.compare Value.compare) tests)
                               ~f ~post
  in { (create_positive ~f ~args ~post ~features pos) with
       neg_tests = List.map neg ~f:(fun t -> (t, lazy (compute_feature_vector t features)))
     }

let add_pos_test ~(job : t) (test : Value.t list) : t =
  if List.exists job.pos_tests ~f:(fun (pt, _) -> pt = test)
  then raise (Duplicate_Test ("New POS test (" ^ (String.concat ~sep:"," job.farg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ "), already exists in POS set!"))
  else if List.exists job.neg_tests ~f:(fun (nt, _) -> nt = test)
  then raise (Ambiguous_Test ("New POS test (" ^ (String.concat ~sep:"," job.farg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in NEG set!"))
  else try if job.post test (Result.try_with (fun () -> job.f test))
           then {
                  job with
                  pos_tests = (test, lazy (compute_feature_vector test job.features))
                           :: job.pos_tests
                }
           else raise (Ambiguous_Test "")
       with _ -> raise (Ambiguous_Test ("New POS test (" ^ (String.concat ~sep:"," job.farg_names)
                                       ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                                       ^ "), does not belong in POS set!"))

let add_neg_test ~(job : t) (test : Value.t list) : t =
  if List.exists job.neg_tests ~f:(fun (nt, _) -> nt = test)
  then raise (Duplicate_Test ("New NEG test (" ^ (String.concat ~sep:"," job.farg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in NEG set!"))
  else if List.exists job.pos_tests ~f:(fun (pt, _) -> pt = test)
  then raise (Ambiguous_Test ("New NEG test (" ^ (String.concat ~sep:"," job.farg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in POS set!"))
  else try if job.post test (Result.try_with (fun () -> job.f test))
           then raise (Ambiguous_Test "")
           else raise Caml.Exit
       with Ambiguous_Test _ | IgnoreTest
            -> raise (Ambiguous_Test ("New NEG test (" ^ (String.concat ~sep:"," job.farg_names)
                                     ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                                     ^ ") does not belong in NEG set!"))
          | Caml.Exit -> {
              job with
              neg_tests = (test, lazy (compute_feature_vector test job.features))
                      :: job.neg_tests
          }

let add_feature ~(job : t) (feature : 'a feature with_desc) : t =
  let add_to_fv (t, old_fv) =
    (t, lazy ((compute_feature_value t feature) :: (Lazy.force old_fv)))
  in { job with
       features = feature :: job.features ;
       pos_tests = List.map job.pos_tests ~f:add_to_fv ;
       neg_tests = List.map job.neg_tests ~f:add_to_fv ;
     }