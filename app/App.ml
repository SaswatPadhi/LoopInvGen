open Base
open LoopInvGen

(* a job for inferring a precondition to ensure that the absolute value
   function has a result equal to its argument *)
let abs_job = Job.create
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (if x > 0 then x else -x))
  ~args:([ "x", Type.INT ])
  ~post:(fun inp res ->
           match inp , res with
           | [ Value.Int x ], Ok (Value.Int y) -> x = y
           | _ -> false)
  ~features:[
    ((fun [@warning "-8"] [Value.Int x] -> x > 0), "(> x 0)")
  ]
  (List.map [(-1) ; 3 ; 0 ; (-2) ; 6] ~f:(fun i -> [Value.Int i]))


let print_PI_results (result, stats) =
  let open PIE in
  Stdio.(Out_channel.output_lines stdout [
    ("The precondition is: " ^ (cnf_opt_to_desc result)) ;
    ("  > Total time (ms): " ^ (Float.to_string stats.pi_time_ms)) ;
    ("  > Synth time (ms): [" ^ (Utils.List.to_string_map
                                    ~sep:"; " stats._Synthesizer
                                    ~f:(fun s -> Float.to_string (s.synth_time_ms)))
                              ^ "]") ;
    ""
  ])

let no_synth_PI () =
  Stdio.print_endline "Precondition inference without feature learning:" ;
  print_PI_results (PIE.learnPreCond abs_job ~conf:{ PIE.default_config
                                                     with disable_synth = true })

let with_synth_PI () =
  Stdio.print_endline "Precondition inference with feature learning:" ;
  print_PI_results (PIE.learnPreCond abs_job)

let () = no_synth_PI ()
       ; with_synth_PI ()
