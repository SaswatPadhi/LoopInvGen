
open Core
open Core.Out_channel

let parse s : string = 
  let lexbuf = Lexing.from_string (s ^ "\n") in
  let ast = UserFunParser.main UserFunLexer.token lexbuf in
  ast

let main outfile filename () =
  let out_chan = (match outfile with
  | None -> Out_channel.stdout
  | Some filename -> Out_channel.create filename) in
  let inputlines = In_channel.read_lines filename in
  List.map inputlines ~f:(fun i -> output_string out_chan (parse i))

let spec =
  let open Command.Spec in (
      empty
      +> flag "-o" (optional string)  ~doc:"FILENAME output file for invariant, defaults to stdout"
      +> anon (maybe_with_default "-" ("filename" %: file))
    )

let cmd =
  Command.basic_spec spec main
    ~summary: "Parses user inputs from Sorin."

let () =
  Command.run
    ~version:"0.6b"
    ~build_info:("padhi @ " ^ (Core_extended.Logger.timestamp ()))
    cmd
