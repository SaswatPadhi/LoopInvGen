open Core

open LoopInvGen

let command =
  let open Command.Let_syntax in
  Command.basic
    ~summary: "Record program states for a given SyGuS-INV benchmark."
    [%map_open
      let z3_path       = flag "z3-path" (required string)
                               ~doc:"FILENAME path to the z3 executable"
      and states_count  = flag "states-count" (optional_with_default 512 int)
                               ~doc:"COUNT number of steps to simulate"
      and random_seed   = flag "random-seed" (optional string)
                               ~doc:"STRING seed for the internal PRNG"
      and log_path      = flag "log-path" (optional string)
                                ~doc:"FILENAME enable logging and output to the specified path"
      and sygus_path    = anon ("filename" %: string)
      in fun () ->
        Log.enable ~msg:"RECORD" log_path ;
        let sygus = SyGuS.read_from sygus_path
         in begin if states_count < 1 then ()
                  else StateSampler.record_states sygus ~zpath:z3_path ~size:states_count
                         ~state_chan:Stdio.Out_channel.stdout
                         ~seed:(match random_seed with
                                | None -> `Nondeterministic
                                | Some seed -> `Deterministic seed)
            end
    ]

let () =
  Command.run command
