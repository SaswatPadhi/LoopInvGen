open Core

open LoopInvGen

let output_stats stats = function
  | None -> ()
  | Some statsfile
    -> let stats_chan = Out_channel.create statsfile
        in Out_channel.output_string stats_chan
             (Sexplib.Sexp.to_string_hum ~indent:4 (LIG.sexp_of_stats stats))
         ; Out_channel.close stats_chan

let config_flags =
  let open Command.Let_syntax in
  [%map_open
    let base_random_seed          = flag "base-random-seed"
                                         (optional_with_default LIG.Config.default.base_random_seed string)
                                         ~doc:"STRING seed for the internal PRNG"
    and do_simplify               = flag "do-simplify"
                                         (optional_with_default LIG.Config.default._VPIE.do_simplify bool)
                                         ~doc:"BOOLEAN simplify all synthesized expressions using Z3"
    and max_attempts              = flag "max-attempts"
                                         (optional_with_default LIG.Config.default._VPIE.max_attempts int)
                                         ~doc:"BOOLEAN maximum number of attempts before restarting"
    and max_conflict_group_size   = flag "max-conflict-group-size"
                                         (optional_with_default LIG.Config.default._VPIE._PIE.max_conflict_group_size int)
                                         ~doc:"INTEGER maximum size of the conflict group to send to the synthesizer"
    and max_expressiveness_level  = flag "max-expressiveness-level"
                                         (optional_with_default LIG.Config.default._VPIE._PIE._Synthesizer.max_expressiveness_level int)
                                         ~doc:"INTEGER maximum expressiveness level {1 = Equalities ... 6 = Peano Arithmetic}"
    and max_steps_on_restart      = flag "max-steps-on-restart"
                                         (optional_with_default LIG.Config.default.max_steps_on_restart int)
                                         ~doc:"INTEGER number of new states to collect after a restart"
    and num_counterexamples       = flag "num-counterexamples"
                                         (optional_with_default LIG.Config.default._VPIE.num_counterexamples int)
                                         ~doc:"INTEGER number of counterexamples to collect for each invalid precondition"
    in {
      LIG.Config.default with
      _VPIE = {
        LIG.Config.default._VPIE with
        _PIE = {
          LIG.Config.default._VPIE._PIE with
          _Synthesizer = {
            LIG.Config.default._VPIE._PIE._Synthesizer with
            max_expressiveness_level
          }
        ; max_conflict_group_size
        }
      ; max_attempts
      ; num_counterexamples
      ; do_simplify
      }
    ; base_random_seed
    ; max_steps_on_restart
    }
  ]

let read_and_permute_states states_chan =
  List.(permute ~random_state:(Random.State.make [| 79 ; 97 |])
                (map (Stdio.In_channel.input_lines states_chan)
                    ~f:(fun l -> map (String.split ~on:'\t' l) ~f:Value.of_string)))

let command =
  let open Command.Let_syntax in
  Command.basic
    ~summary: "Infer a loop invariant sufficient for proving the correctness of the input problem."
    [%map_open
      let states_path        = flag "states-path" (required string)
                                    ~doc:"FILENAME path to the file containing sampled program states"
      and z3_path            = flag "z3-path" (required string)
                                     ~doc:"FILENAME path to the z3 executable"
      and log_path           = flag "log-path" (optional string)
                                    ~doc:"FILENAME enable logging and output to the specified path"
      and neg_states_path    = flag "neg-states-path" (optional string)
                                    ~doc:"FILENAME path to the file containing sampled negative states"
      and report_path        = flag "report-path" (optional string)
                                    ~doc:"FILENAME report statistics (time and counterexamples) to the specified path"
      and user_features_path = flag "features-path" (optional string)
                                    ~doc:"FILENAME initial features to preseed the learner with"
      and config             = config_flags
      and sygus_path         = anon ("filename" %: string)
      in fun () -> begin
        Log.enable ~msg:"INFER" log_path ;
        let states_chan = Utils.get_in_channel states_path in
        let states = read_and_permute_states states_chan
        and neg_states = match neg_states_path with
                         | None -> []
                         | Some neg_states_path
                           -> let neg_states_chan = Stdio.In_channel.create neg_states_path in
                              let neg_states = read_and_permute_states neg_states_chan
                               in Stdio.In_channel.close neg_states_chan
                                ; neg_states
         in Stdio.In_channel.close states_chan
          ; Log.debug (lazy ("Loaded " ^ (Int.to_string (List.length states)) ^ " states."))
          ; let sygus = SyGuS.read_from sygus_path in
            let logic = Logic.of_string sygus.logic in
            let user_input = (match user_features_path with
                              | Some path -> In_channel.read_lines path
                              | None -> []) in
            let config = {
              config with
              _VPIE = {
                config._VPIE with
                _PIE = {
                  config._VPIE._PIE with
                  _Synthesizer = { config._VPIE._PIE._Synthesizer with logic }
                ; max_conflict_group_size = logic.sample_set_size_multiplier
                                          * config._VPIE._PIE.max_conflict_group_size
                }
              ; num_counterexamples = logic.sample_set_size_multiplier
                                    * config._VPIE.num_counterexamples
              }
              ; user_features = Utils.make_user_features user_input sygus.synth_variables
            }
            in let inv, stats = LIG.learnInvariant ~config ~zpath:z3_path ~states ~neg_states sygus
            in Out_channel.output_string
                 Stdio.stdout
                 SyGuS.(func_definition { sygus.inv_func with body = (translate_smtlib_expr inv) })
             ; output_stats stats report_path
      end
    ]

let () =
  Command.run command
