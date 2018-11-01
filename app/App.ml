open Base
open LoopInvGen

let () =
  Stdio.print_endline (
      "The default synthesis logic is: "
    ^ (PIE.default_config.synth_logic.name)
  )