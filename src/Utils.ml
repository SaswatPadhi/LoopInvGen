open Base

module Hashtbl = struct
  include Hashtbl

  let find_default (tbl : ('a, 'b) Hashtbl.t) (key : 'a) ~(default : 'b) : 'b =
    Option.value (Hashtbl.find tbl key) ~default
end

module List = struct
  include List

  let cons_opt_value (o : 'a option) (l : 'a list) : 'a list =
    match o with None -> l | Some v -> v :: l

  let to_string_map ~(sep : string) (l : 'a list) ~(f : 'a -> string) : string =
    String.concat ~sep (List.map l ~f)

  let to_string_map2 ~(sep : string) (l1 : 'a list) (l2 : 'b list)
                     ~(f : 'a -> 'b -> string) : string =
    String.concat ~sep (List.map2_exn l1 l2 ~f)

  let range_map ?(stride = 1) ?(start = `inclusive) ?(stop = `exclusive)
                ~(f : int -> 'a) (start_i : int) (stop_i : int) : 'a list =
    List.(map (range ~stride ~start ~stop start_i stop_i) ~f)
end

let get_in_channel = function
  | "-"      -> Stdio.In_channel.stdin
  | filename -> Stdio.In_channel.create filename

let get_out_channel = function
  | None -> Stdio.Out_channel.stdout
  | Some filename -> Stdio.Out_channel.create filename