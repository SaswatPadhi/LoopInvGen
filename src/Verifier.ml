open Core
open Core.Out_channel
open SyGuS
open Utils

let main statefile outfile do_log filename () =
  (if do_log then Log.enable ~msg:"VERIFIER" () else ()) ;
  let in_chan = Utils.get_in_channel statefile
  in let states =
       List.(map (In_channel.input_lines in_chan)
                 ~f:(fun l -> map (Types.deserialize_values l)
                                  ~f:(fun v -> Option.value_exn v)))
  in In_channel.close in_chan
   ; Log.debug (lazy ("Loaded " ^ (string_of_int (List.length states)) ^
                      " program states."))
   ; let sygus = SyGuS.load (Utils.get_in_channel filename)
     in let inv = LoopInvGen.learnInvariant sygus ~states
     in let out_chan = Utils.get_out_channel outfile
     in output_string out_chan (
          "(define-fun " ^ sygus.inv_name ^ " (" ^
          (List.to_string_map sygus.inv_vars ~sep:" "
             ~f:(fun (v, t) -> "(" ^ v ^ " " ^ (Types.string_of_typ t) ^ ")")) ^
          ") Bool " ^ (Option.value inv ~default:"false") ^ ")")
      ; Out_channel.close out_chan

let cmd =
  Command.basic
    ~summary: "Attempts to infer a loop invariant sufficient for proving correctness."
    Command.Spec.(
      empty
      +> flag "-s" (required string)  ~doc:"FILENAME states file containing program states"
      +> flag "-o" (optional string)  ~doc:"FILENAME output file for invariant, defaults to stdout"
      +> flag "-l" (no_arg)           ~doc:"enable logging"
      +> anon (maybe_with_default "-" ("filename" %: file))
    )
    main

let () =
  Command.run
    ~version:"0.6b"
    ~build_info:("padhi @ " ^ (Core_extended.Logger.timestamp ()))
    cmd