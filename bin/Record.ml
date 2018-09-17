open Core
open LoopInvGen

let main zpath size seed logfile filename () =
  Log.enable ~msg:"RECORD" logfile ;
  let sygus = SyGuS.read_from filename
  in if size < 1 then ()
     else Simulator.record_states sygus ~zpath ~size
            ~state_chan:Stdio.Out_channel.stdout
            ~seed:(match seed with
                    | None -> `Nondeterministic
                    | Some seed -> `Deterministic seed)

let spec =
  let open Command.Spec in (
    empty
    +> flag "-z" (required string)
       ~doc:"FILENAME path to the z3 executable"
    +> flag "-s" (optional_with_default 512 int)
       ~doc:"COUNT number of steps to simulate"
    +> flag "-e" (optional string)
       ~doc:"STRING seed for the internal PRNG"
    +> flag "-l" (optional string)
       ~doc:"FILENAME output file for logs, defaults to null"
    +> anon ("filename" %: file)
  )

let () =
  Command.run
    (Command.basic_spec spec main
       ~summary: "Record program states for a given SyGuS-INV benchmark.")
