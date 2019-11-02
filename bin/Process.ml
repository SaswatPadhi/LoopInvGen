open Core

open LoopInvGen

let command =
  let open Command.Let_syntax in
  Command.basic
    ~summary: "Check, simplify, and optimize a SyGuS-INV problem."
    [%map_open
      let z3_path     = flag "z3-path" (required string)
                             ~doc:"FILENAME path to the z3 executable"
      and out_path    = flag "out-path" (required string)
                             ~doc:"FILENAME (binary) output file for the post-processed SyGuS problem"
      and log_path    = flag "log-path" (optional string)
                             ~doc:"FILENAME enable logging and output to the specified path"
      and sygus_path  = anon (maybe_with_default "-" ("filename" %: string))
      in fun () ->
        Log.enable ~msg:"PROCESS" log_path ;
        let in_chan = Utils.get_in_channel sygus_path in
        let sygus = SyGuS.parse (in_chan)
        in SyGuS.(write_to out_path (SyGuS_Opt.optimize sygus))
          ; Stdio.In_channel.close in_chan
          ; let post_as_inv = SyGuS.func_definition { sygus.inv_func with body = sygus.post_func.body }
             in begin match Check.is_sufficient_invariant ~zpath:z3_path ~sygus sygus.post_func.body with
                | PASS -> Out_channel.output_string Stdio.stdout post_as_inv
                | _ -> ()
                end
    ]

let () =
  Command.run command
