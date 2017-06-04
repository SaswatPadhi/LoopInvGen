open Core
open Core.Out_channel

let get_in_channel = function
  | "-"      -> In_channel.stdin
  | filename -> In_channel.create filename

let get_out_channel = function
  | None -> Out_channel.stdout
  | Some filename -> Out_channel.create filename

let main statefile outfile do_log filename () =
  (if do_log then Log.enable ~msg:"VERIFIER" () else ()) ;
  let in_chan = get_in_channel statefile
  in let states =
       List.(map (In_channel.input_lines in_chan)
                 ~f:(fun l -> map (Types.deserialize_values l)
                                  ~f:(fun v -> Option.value_exn v)))
  in In_channel.close in_chan
   ; let sygus = SyGuS.load (get_in_channel filename)
     in let inv = LoopInvGen.learnInvariant sygus ~states
     in let out_chan = get_out_channel outfile
     in output_string out_chan (Option.value inv ~default:"FAILED")
      ; Out_channel.close out_chan

let cmd =
  Command.basic
    ~summary: "Record program states for a given SyGuS-INV benchmark."
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