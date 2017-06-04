open Core
open Core.Out_channel
open Exceptions
open SyGuS

let main size forks seeds outfile do_log filename () =
  (if do_log then Log.enable ~msg:"RECORDER" () else ()) ;
  let s = SyGuS.load (Utils.get_in_channel filename)
  in (if s.state_vars <> s.inv_vars
      then raise (Internal_Exn "Invariant over restricted states."))
   ; if size < 1 then ()
     else begin
       let out_chan = Utils.get_out_channel outfile in
       let seeds = (if seeds = [] then [`Nondeterministic]
                   else List.map ~f:(fun s -> `Deterministic s) seeds)
       in List.iter seeds
           ~f:(fun seed ->
                 newline out_chan ;
                 let states = Simulator.run s ~size ~seed
                 in List.iter states
                       ~f:(fun state ->
                             output_string out_chan (
                               Types.serialize_values state) ;
                             newline out_chan)
               )
       ; Out_channel.close out_chan
     end

let cmd =
  Command.basic
    ~summary: "Record program states for a given SyGuS-INV benchmark."
    Command.Spec.(
      empty
      +> flag "-s" (optional_with_default 512 int) ~doc:"COUNT number of steps to simulate"
      +> flag "-f" (optional_with_default 6 int)   ~doc:"COUNT number of forks to create"
      +> flag "-r" (listed string)                 ~doc:"STRING random-string seed for start state"
      +> flag "-o" (optional string)               ~doc:"FILENAME output file for states, defaults to stdout"
      +> flag "-l" (no_arg)                        ~doc:"enable logging"
      +> anon (maybe_with_default "-" ("filename" %: file))
    )
    main

let () =
  Command.run
    ~version:"0.6b"
    ~build_info:("padhi @ " ^ (Core_extended.Logger.timestamp ()))
    cmd