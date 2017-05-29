open Core
open Core.Out_channel

let get_in_channel = function
  | "-"      -> In_channel.stdin
  | filename -> In_channel.create filename

let get_out_channel = function
  | None -> Out_channel.stdout
  | Some filename -> Out_channel.create filename

let main size forks seeds outfile metafile do_log do_names filename () =
  (if do_log then Log.enable() else ()) ;
  let open Sygus in
  let meta_chan = get_out_channel metafile in
  let s = load (get_in_channel filename)
  in output_string meta_chan "Detected constants:\n  "
   ; output_string meta_chan (Types.serialize_values s.consts) ; newline meta_chan
   ; output_string meta_chan "Detected variables:\n"
   ; output_string meta_chan (vars_to_string s) ; newline meta_chan
   ; if size < 1 then () else begin
       let out_chan = get_out_channel outfile in
       let seeds = (if seeds = [] then [`Nondeterministic]
                    else List.map ~f:(fun s -> `Deterministic s) seeds)
       in List.iter seeds
           ~f:(fun seed ->
                 newline out_chan ;
                 let states = Simulator.run s ~size ~seed
                 in List.iter states
                       ~f:(fun state ->
                             output_string out_chan (state_to_string s state ~names:(do_names))
                                     ; newline out_chan)
               )
       ; Out_channel.close out_chan
     end
   ; Out_channel.close meta_chan

let cmd =
  Command.basic
    ~summary: "Record program states for a given SyGuS-INV benchmark."
    Command.Spec.(
      empty
      +> flag "-s" (optional_with_default 512 int) ~doc:"COUNT number of steps to simulate"
      +> flag "-f" (optional_with_default 6 int)   ~doc:"COUNT number of forks to create"
      +> flag "-r" (listed string)                 ~doc:"STRING random-string seed for start state"
      +> flag "-o" (optional string)               ~doc:"FILENAME output file for states, defaults to stdout"
      +> flag "-m" (optional string)               ~doc:"FILENAME output file for metadata, defaults to stdout"
      +> flag "-l" (no_arg)                        ~doc:"enable logging"
      +> flag "-n" (no_arg)                        ~doc:"print variable names"
      +> anon (maybe_with_default "-" ("filename" %: file))
    )
    main

let () =
  Command.run
    ~version:"0.6b"
    ~build_info:("padhi @ " ^ (Core_extended.Logger.timestamp ()))
    cmd