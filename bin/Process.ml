open Core
open LoopInvGen

let main outfile logfile filename () =
  Log.enable ~msg:"PROCESS" logfile ;
  let in_chan = Utils.get_in_channel filename
   in SyGuS.(write_to outfile (SyGuS_Opt.optimize (parse (in_chan))))
    ; Stdio.In_channel.close in_chan

let spec =
  let open Command.Spec in (
    empty
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
