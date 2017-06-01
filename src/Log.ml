open Core_extended.Logger

let logger = create_default "_logs/SyGuSPIE.log"
let () = clear_filter logger

let enabled = ref false

let fatal lstr = if !enabled then log logger (`Fatal , (Lazy.force lstr)) else ()
let error lstr = if !enabled then log logger (`Error , (Lazy.force lstr)) else ()
let warn  lstr = if !enabled then log logger (`Warn  , (Lazy.force lstr)) else ()
let info  lstr = if !enabled then log logger (`Info  , (Lazy.force lstr)) else ()
let debug lstr = if !enabled then log logger (`Debug , (Lazy.force lstr)) else ()

let disable () = enabled := false
let enable ?(msg = "") () =
  enabled := true ;
  info (lazy "") ;
  info (lazy (msg ^ "========================================"))