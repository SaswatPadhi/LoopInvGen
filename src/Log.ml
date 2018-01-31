open Core_extended.Logger

let logger = ref (create_default "")

let enabled = ref false
let indented_sep (indent : int) = "\n" ^ (Core.String.make (42 + indent) ' ')

let fatal lstr = if !enabled then log (!logger) (`Fatal , (Lazy.force lstr)) else ()
let error lstr = if !enabled then log (!logger) (`Error , (Lazy.force lstr)) else ()
let warn  lstr = if !enabled then log (!logger) (`Warn  , (Lazy.force lstr)) else ()
let info  lstr = if !enabled then log (!logger) (`Info  , (Lazy.force lstr)) else ()
let debug lstr = if !enabled then log (!logger) (`Debug , (Lazy.force lstr)) else ()

let disable () = enabled := false
let enable ?(msg = "") (file : string) =
  logger := create_default file ;
  clear_filter (!logger) ;
  enabled := true ;
  info (lazy "") ;
  info (lazy (msg ^ "========================================"))