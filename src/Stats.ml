open Base

module Synth = struct
  type t = {
    enumerated : int ;
    pruned : int ;
    time_ms : float
  } [@@deriving sexp]
end

module Infer = struct
  type t = {
    guesses : int ;
    time_ms : float
  } [@@deriving sexp]
end

module Stats_Internal = struct
  let candidates : int ref = ref 0
  let rev_synths : Synth.t list ref = ref []
  let rev_infers : Infer.t list ref = ref []
end

let add_candidate () = Stats_Internal.candidates := 1 + (!Stats_Internal.candidates)
let add_synth (s : Synth.t) = Stats_Internal.rev_synths := s :: (!Stats_Internal.rev_synths)
let add_infer (i : Infer.t) = Stats_Internal.rev_infers := i :: (!Stats_Internal.rev_infers)

let candidates () = !Stats_Internal.candidates
let synths () = List.rev (!Stats_Internal.rev_synths)
let infers () = List.rev (!Stats_Internal.rev_infers)

let output_to (filename : string option) =
  match filename with
  | None -> ()
  | Some fname
    -> let open Stdio.Out_channel in
       let stats_channel = create fname
        in output_lines stats_channel [
             ("Candidate Invariants Explored = " ^ (Int.to_string (!Stats_Internal.candidates)))
           ; ("Total Number of Counterexamples = "
             ^ (Int.to_string (List.fold (!Stats_Internal.rev_infers) ~init:0 ~f:(fun a i -> a + i.guesses))))
           ; ("Total Number of Expressions Enumerated = "
             ^ (Int.to_string (List.fold (!Stats_Internal.rev_synths) ~init:0 ~f:(fun a s -> a + s.enumerated))))
           ; ("Average Time Spent in Synthesis (ms) = "
             ^ (Float.to_string ((List.fold (!Stats_Internal.rev_synths) ~init:0.0 ~f:(fun a s -> a +. s.time_ms))
                                 /. (Int.to_float (List.length (!Stats_Internal.rev_synths))))))
           ; ""
           ; "Detailed Stats for Precondition Inference: (VPIE calls)"
         ]
         ; output_lines stats_channel
                        (List.rev_map (!Stats_Internal.rev_infers)
                                      ~f:(fun i -> Sexp.to_string_hum ~indent:2 (Infer.sexp_of_t i)))
         ; output_lines stats_channel [ "" ; "Detailed Stats for Synthesis: (Synthesizer calls)" ]
         ; output_lines stats_channel
                        (List.rev_map (!Stats_Internal.rev_synths)
                                      ~f:(fun s -> Sexp.to_string_hum ~indent:2 (Synth.sexp_of_t s)))
         ; close stats_channel
