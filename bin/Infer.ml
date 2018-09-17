open Core
open LoopInvGen

let main zpath statefile logfile max_conflicts max_strengthening_attempts
         max_restarts max_steps_on_restart filename () =
  Log.enable ~msg:"INFER" logfile ;
  let state_chan = Utils.get_in_channel statefile in
  let states = List.(permute
    ~random_state:(Random.State.make [| 79 ; 97 |])
    (map (Stdio.In_channel.input_lines state_chan)
         ~f:(fun l -> map (String.split ~on:'\t' l) ~f:Value.of_string)))
  in Stdio.In_channel.close state_chan
   ; Log.debug (lazy ("Loaded " ^ (Int.to_string (List.length states)) ^
                      " program states."))
   ; let sygus = SyGuS.read_from filename
     in let logic = Logic.of_string sygus.logic
     in let conf = {
       LIG.default_config with
       for_VPIE = {
         LIG.default_config.for_VPIE with
         for_PIE = {
           LIG.default_config.for_VPIE.for_PIE with
           synth_logic = logic;
           max_conflict_group_size = (if max_conflicts > 0 then max_conflicts
                                      else (logic.conflict_group_size_multiplier
                                            * PIE.base_max_conflict_group_size)) ;
         }
       ; max_tries = max_strengthening_attempts
       }
     ; max_restarts
     ; max_steps_on_restart
     }
     in let inv = LIG.learnInvariant ~conf ~zpath ~states sygus
     in Stdio.Out_channel.output_string Stdio.Out_channel.stdout
          SyGuS.(func_definition {sygus.inv_func with expr=(translate_smtlib_expr inv)})
      ; Caml.exit (if String.equal inv "false" then 1 else 0)

let spec =
  let open Command.Spec in (
      empty
      +> flag "-z" (required string)
         ~doc:"FILENAME path to the z3 executable"
      +> flag "-s" (required string)
         ~doc:"FILENAME states file, containing program states"
      +> flag "-l" (optional string)
         ~doc:"FILENAME enable logging"

      +> flag "-max-conflicts" (optional_with_default 0 int)
         ~doc:"NUMBER max size of the conflict group (POS+NEG). 0 = auto"
      +> flag "-max-strengthening-attempts" (optional_with_default (LIG.default_config.for_VPIE.max_tries) int)
         ~doc:"NUMBER max candidates to consider, per strengthening. 0 = unlimited"
      +> flag "-max-restarts" (optional_with_default (LIG.default_config.max_restarts) int)
         ~doc:"NUMBER number of times the inference engine may restart"
      +> flag "-max-steps-on-restart" (optional_with_default (LIG.default_config.max_steps_on_restart) int)
         ~doc:"NUMBER number of states to collect after each restart"

      +> anon ("filename" %: file)
    )

let () =
  Command.run
    (Command.basic_spec spec main
       ~summary: "Infer a loop invariant sufficient for proving the correctness of the input problem in SyGuS format.")
