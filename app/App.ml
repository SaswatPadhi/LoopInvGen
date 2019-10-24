open Core_kernel

open LoopInvGen

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

(* a job for inferring a precondition to ensure that the absolute value
   function has a result equal to its argument *)
let abs_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (if x > 0 then x else -x))
  ~args:([ ("x", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ], Ok (Value.Int y) -> x = y)
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.INT))))

let with_synth_PI () =
  Stdio.print_endline "PI for { x = abs(x) } with feature learning:" ;
  print_PI_results (PIE.learnPreCond abs_job)


(* a job for inferring a precondition to check when the result of appending
   two lists is an empty list *)
let append_job =
  let open Value
   in Job.create_unlabeled
        ~f:(fun [@warning "-8"] [ List x ; List y ] -> List (x @ y))
        ~args:([ ("x", Type.LIST) ; ("y", Type.LIST) ])
        ~post:(fun inp res ->
                match [@warning "-8"] inp , res with
                | [ List _ ; List _ ] , Ok (List z) -> List z = List [])
        (* We start with these two features and disable feature synthesis *)
        ~features:[
          ((fun [@warning "-8"] [ x ; _ ] -> x = List []), "(= x [])") ;
          ((fun [@warning "-8"] [ _ ; y ] -> y = List []), "(= y [])") ;
        ]
        (* Generators for Type.LIST are not yet implemented. *)
        (List.map [ ([], [])
                  ; ([Int 1 ; Int 2], [Int 3])
                  ; ([Int 4], [])
                  ; ([], [Int 5]) ]
                  ~f:(fun (l1,l2) -> [ List l1 ; List l2 ]))

let no_synth_PI () =
  Stdio.print_endline "PI for { append(l1,l2) = [] } without feature learning:" ;
  print_PI_results (
    PIE.learnPreCond append_job
                     ~config:{ PIE.Config.default with disable_synth = true }
  )


let () = with_synth_PI ()
       ; no_synth_PI ()