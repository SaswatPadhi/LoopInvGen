open Core

open LoopInvGen

let main zpath outfile logfile filename () =
  Log.enable ~msg:"PROCESS" logfile ;
  let in_chan = Utils.get_in_channel filename in
  let sygus = SyGuS.parse (in_chan)
   in SyGuS.(write_to outfile (SyGuS_Opt.optimize sygus))
    ; Stdio.In_channel.close in_chan
    ; let post_as_inv = SyGuS.func_definition { sygus.inv_func with body = sygus.post_func.body }
       in match Check.is_sufficient_invariant ~zpath ~sygus sygus.post_func.body with
          | PASS -> Out_channel.output_string Stdio.stdout post_as_inv
          | _ -> ()

let spec =
  let open Command.Spec in (
    empty
    +> flag "-z" (required string)
       ~doc:"FILENAME path to the z3 executable"
    +> flag "-o" (required string)
       ~doc:"FILENAME (binary) output file for the post-processed SyGuS problem"
    +> flag "-l" (optional string)
       ~doc:"FILENAME output file for logs, defaults to null"
    +> anon (maybe_with_default "-" ("filename" %: file))
  )

let () =
  Command.run
    (Command.basic_spec spec main
       ~summary: "Check, simplify, and optimize a SyGuS-INV problem.")
