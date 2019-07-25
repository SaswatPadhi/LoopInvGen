let indented_sep (indent : int) = "\n" ^ (String.make (42 + indent) ' ')

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

  open Async

  let logger = ref (Log.create ~level:`Error ~output:[] ~on_error:`Raise)

  let is_enabled = ref false
  let do_log ~tags level lstr =
    let open Core
     in prerr_endline (Lazy.force lstr)
    (* if !is_enabled then Log.string !logger ~tags ~level (Lazy.force lstr) *)

  let error ?(tags = []) lstr = do_log ~tags `Error lstr
  let info ?(tags = []) lstr = do_log ~tags `Info lstr
  let debug ?(tags = []) lstr = do_log ~tags `Debug lstr

  let disable () = is_enabled := false

  let enable ?(msg = "") ?(level = `Debug) = function
    | None -> ()
    | Some filename
      -> logger := Log.create ~level ~output:[ Log.Output.file `Text ~filename ]
                              ~on_error:(`Call (fun err -> error (lazy (Core.Error.to_string_hum err))))
       ; is_enabled := true
       ; info (lazy "")
       ; info (lazy (msg ^ String.(make (79 - (length msg)) '=')))
[%%endif]
