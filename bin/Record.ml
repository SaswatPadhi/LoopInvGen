open Core
open LoopInvGen

let main zpath size seed statefile logfile filename () =
  Log.enable ~msg:"RECORD" logfile ;
  let sygus = SyGuS.read_from filename
  in if size < 1 then ()
     else begin
       let state_chan = Utils.get_out_channel statefile
       in Simulator.record_states sygus ~zpath ~size ~state_chan
            ~seed:(match seed with
                   | None -> `Nondeterministic
                   | Some seed -> `Deterministic seed)
        ; Out_channel.close state_chan
     end

let spec =
  let open Command.Spec in (
    empty
    +> flag "-z" (required string)                ~doc:"FILENAME path to the z3 executable"
    +> flag "-s" (optional_with_default 512 int)  ~doc:"COUNT number of steps to simulate"
    +> flag "-e" (optional string)                ~doc:"STRING seed for the internal PRNG"
    +> flag "-o" (optional string)                ~doc:"FILENAME output file for states, defaults to stdout"
    +> flag "-l" (optional string)                ~doc:"FILENAME output file for logs, defaults to null"
    +> anon ("filename" %: file)
  )

let () =
  Command.run
    (Command.basic_spec spec main
       ~summary: "Record program states for a given SyGuS-INV benchmark.")