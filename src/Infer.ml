open Core
open Core.Out_channel
open SyGuS
open Utils

let main zpath statefile outfile logfile do_false filename () =
  Utils.start_logging_to ~msg:"INFER" logfile ;
  let state_chan = Utils.get_in_channel statefile in
  let states = List.(map (In_channel.input_lines state_chan)
                       ~f:(fun l -> map (Types.deserialize_values l)
                                        ~f:(fun v -> Option.value_exn v)))
  in In_channel.close state_chan
   ; Log.debug (lazy ("Loaded " ^ (string_of_int (List.length states)) ^
                      " program states."))
   ; let sygus = SyGuS.load (Utils.get_in_channel filename)
     in let sygus_logic = Types.logic_of_string sygus.logic
     in let conf = {
       LoopInvGen.default_config with for_VPIE = {
         LoopInvGen.default_config.for_VPIE with for_PIE = {
           LoopInvGen.default_config.for_VPIE.for_PIE
           with synth_logic = sygus_logic;
                max_c_group_size = (PIE.conflict_group_size_multiplier_for_logic sygus_logic) * PIE.base_max_conflict_group_size;
         }
       }
     }
     in let inv = LoopInvGen.learnInvariant ~conf ~zpath ~states sygus
     in let out_chan = Utils.get_out_channel outfile
     in if (not do_false) && inv = "false" then ()
        else output_string out_chan ((build_inv_func (ZProc.normalize inv) ~sygus) ^ "\n")
      ; Out_channel.close out_chan
      ; exit (if inv = "false" then 1 else 0)

let cmd =
  Command.basic_spec
    ~summary: "Attempts to infer a loop invariant sufficient for proving correctness."
    Command.Spec.(
      empty
      +> flag "-z" (required string)  ~doc:"FILENAME path to the z3 executable"
      +> flag "-s" (required string)  ~doc:"FILENAME states file, containing program states"
      +> flag "-o" (optional string)  ~doc:"FILENAME output file for invariant, defaults to stdout"
      +> flag "-l" (optional string)  ~doc:"FILENAME enable logging"
      +> flag "-f" (no_arg)           ~doc:"force generate `false` as the invariant, in case of failure"
      +> anon (maybe_with_default "-" ("filename" %: file))
    )
    main

let () =
  Command.run
    ~version:"0.6b"
    ~build_info:("padhi @ " ^ (Core_extended.Logger.timestamp ()))
    cmd
