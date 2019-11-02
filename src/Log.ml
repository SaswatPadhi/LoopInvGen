let indented_sep (indent : int) = "\n" ^ (String.make (45 + indent) ' ')

[%%import "config.h"]

[%%if LOGGING = 0]
  (* If logging has been entirely disabled during compilation *)
  let fatal _ = ()
  let error _ = ()
  let warn  _ = ()
  let info  _ = ()
  let debug _ = ()

  let disable () = ()

  let [@warning "-27"] enable ?msg ?level _ = ()
[%%else]
  (* If logging has not been disabled, a user may still choose not to log
   * during a particular execution. Logging functions therefore accept `lazy`
   * strings that are forced only when they are actually logged. *)

  open Core

  type level = Debug | Error | Info
  let level_str = function Debug -> "( debug )"
                         | Error -> "< ERROR >"
                         | Info  -> "(  info )"
  let log_chan = ref stderr
  let log_level = ref Debug

  let is_enabled = ref false
  let should_log level =
    if not !is_enabled then false
    else match level, !log_level with
         | Error , _ | Info , Info | _ , Debug -> true
         | _ -> false

  let do_log level lstr =
    if should_log level
    then begin
      Out_channel.fprintf
        !log_chan
        "%s  %s  %s\n"
        Time.(to_string (now ()))
        (level_str level)
        (Lazy.force lstr)
    end

  let info lstr = do_log Info lstr
  let debug lstr = do_log Debug lstr
  let error lstr = do_log Error lstr

  let disable () = is_enabled := false

  let enable ?(msg = "") ?(level = Debug) = function
    | None -> ()
    | Some filename
      -> log_chan := Out_channel.create ~append:true filename
       ; log_level := level
       ; is_enabled := true
       ; info (lazy "")
       ; info (lazy (msg ^ String.(make (79 - (length msg)) '=')))
[%%endif]
