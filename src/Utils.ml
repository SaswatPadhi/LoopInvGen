open Base

module Hashtbl = struct
  include Hashtbl

  let find_default (tbl : ('a, 'b) Hashtbl.t) (key : 'a) ~(default : 'b) : 'b =
    Option.value (Hashtbl.find tbl key) ~default
end

module List = struct
  include List

  let to_string_map ~(sep : string) (l : 'a list) ~(f : 'a -> string) : string =
    String.concat ~sep (List.map l ~f)

  let to_string_mapi ~(sep : string) (l : 'a list) ~(f : int -> 'a -> string) : string =
    String.concat ~sep (List.mapi l ~f)

  let to_string_map2 ~(sep : string) (l1 : 'a list) (l2 : 'b list)
                     ~(f : 'a -> 'b -> string) : string =
    String.concat ~sep (List.map2_exn l1 l2 ~f)

  let range_map ?(stride = 1) ?(start = `inclusive) ?(stop = `exclusive)
                ~(f : int -> 'a) (start_i : int) (stop_i : int) : 'a list =
    List.(map (range ~stride ~start ~stop start_i stop_i) ~f)
end

module Array = struct
  include Array

  let to_string_map ~(sep : string) (l : 'a array) ~(f : 'a -> string) : string =
    String.concat_array ~sep (Array.map l ~f)

  let to_string_map2 ~(sep : string) (l1 : 'a array) (l2 : 'b array)
                     ~(f : 'a -> 'b -> string) : string =
    String.concat_array ~sep (Array.map2_exn l1 l2 ~f)
end

let get_in_channel = function
  | "-"      -> Stdio.In_channel.stdin
  | filename -> Stdio.In_channel.create filename
