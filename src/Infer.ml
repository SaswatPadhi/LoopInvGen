open Core

let main zpath statefile outfile logfile false_on_failure
         max_conflicts max_strengthening_attempts
         max_restarts max_steps_on_restart
         filename () =
  Log.enable ~msg:"INFER" logfile ;
  let state_chan = Utils.get_in_channel statefile in
  let states = List.(permute
    ~random_state:(Random.State.make [| 79 ; 97 |])
    (map (Stdio.In_channel.input_lines state_chan)
         ~f:(fun l -> map (Types.deserialize_values l)
                          ~f:(fun v -> Option.value_exn v))))
  in Stdio.In_channel.close state_chan
   ; Log.debug (lazy ("Loaded " ^ (Int.to_string (List.length states)) ^
                      " program states."))
   ; let sygus = SyGuS.read_from filename
     in let synth_logic = Types.logic_of_string sygus.logic
     in let conf = {
       LoopInvGen.default_config with
       for_VPIE = {
         LoopInvGen.default_config.for_VPIE with
         for_PIE = {
           LoopInvGen.default_config.for_VPIE.for_PIE with
           synth_logic;
           max_conflict_group_size = (if max_conflicts > 0 then max_conflicts
                                      else ((PIE.conflict_group_size_multiplier_for_logic synth_logic)
                                            * PIE.base_max_conflict_group_size)) ;
         }
       ; max_tries = max_strengthening_attempts
       }
     ; max_restarts
     ; max_steps_on_restart
     }
     in let inv = LoopInvGen.learnInvariant ~conf ~zpath ~states sygus
     in let out_chan = Utils.get_out_channel outfile
     in if (not false_on_failure) && (String.equal inv "false") then ()
        else Stdio.Out_channel.output_string out_chan
               SyGuS.(func_definition {sygus.inv_func with expr=(translate_smtlib_expr inv)})
      ; Stdio.Out_channel.close out_chan
      ; Caml.exit (if String.equal inv "false" then 1 else 0)

let spec =
  let open Command.Spec in (
      empty
      +> flag "-z" (required string)  ~doc:"FILENAME path to the z3 executable"
      +> flag "-s" (required string)  ~doc:"FILENAME states file, containing program states"
      +> flag "-o" (optional string)  ~doc:"FILENAME output file for invariant, defaults to stdout"
      +> flag "-l" (optional string)  ~doc:"FILENAME enable logging"
      +> flag "-f" (no_arg)           ~doc:"generate `false` instead of an empty invariant, in case of failure"

      +> flag "-max-conflicts"              (optional_with_default 0 int)
                                            ~doc:"NUMBER max size of the conflict group (POS+NEG). 0 = auto"
      +> flag "-max-strengthening-attempts" (optional_with_default (LoopInvGen.default_config.for_VPIE.max_tries) int)
                                            ~doc:"NUMBER max candidates to consider, per strengthening. 0 = unlimited"
      +> flag "-max-restarts"               (optional_with_default (LoopInvGen.default_config.max_restarts) int)
                                            ~doc:"NUMBER number of times the inference engine may restart"
      +> flag "-max-steps-on-restart"       (optional_with_default (LoopInvGen.default_config.max_steps_on_restart) int)
                                            ~doc:"NUMBER number of states to collect after each restart"

      +> anon ("filename" %: file)
    )

let () =
  Command.run
    (Command.basic_spec spec main
       ~summary: "Infer a loop invariant sufficient for proving the correctness of the input problem in SyGuS format.")