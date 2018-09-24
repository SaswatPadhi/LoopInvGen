open Core

let parse (s : string) : string =
  Parser.main Lexer.token (Lexing.from_string (s ^ "\n"))

let command =
  let open Command.Let_syntax in
  Command.basic
    ~summary: "Parses user inputs for InvGame project"
    [%map_open
      let feature_file = anon ("FILENAME" %: string)
       in fun () ->
            let inputs = In_channel.read_lines feature_file in
            let outputs = List.map inputs ~f:parse
             in Out_channel.output_lines stdout outputs
    ]

let () =
  Command.run command