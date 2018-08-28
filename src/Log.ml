let indented_sep (indent : int) = "\n" ^ (String.make (42 + indent) ' ')

[%%import "config.h"]

[%%if LOGGING = 0]
  let fatal _ = ()
  let error _ = ()
  let warn  _ = ()
  let info  _ = ()
  let debug _ = ()

  let disable () = ()

  let [@warning "-27"] enable ?msg ?level _ = ()
[%%else]
  open Core_extended.Logger

  let logger = ref (create_default "")
  let do_log level lstr = try log (!logger) (level , (Lazy.force lstr)) with _ -> ()

  let enabled = ref 0

  let fatal lstr = if !enabled > 0 then do_log `Fatal lstr
  let error lstr = if !enabled > 1 then do_log `Error lstr
  let warn  lstr = if !enabled > 2 then do_log `Warn lstr
  let info  lstr = if !enabled > 3 then do_log `Info lstr
  let debug lstr = if !enabled > 4 then do_log `Debug lstr

  let disable () = enabled := 0

  let enable ?(msg = "") ?(level = 5) (file : string option) =
    match file with
    | None -> ()
    | Some file -> logger := create_default file
                 ; clear_filter (!logger)
                 ; enabled := level
                 ; info (lazy "")
                 ; info (lazy (msg ^ String.(make (79 - (length msg)) '=')))
[%%endif]