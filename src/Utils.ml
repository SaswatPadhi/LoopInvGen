open Core

module Hashtbl = struct
  include Core.Hashtbl

  let find_default (tbl : ('a, 'b) Hashtbl.t) (key : 'a) ~(default : 'b) : 'b =
    Option.value (Hashtbl.find tbl key) ~default
end

module List = struct
  include Core.List

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
  | "-"      -> In_channel.stdin
  | filename -> In_channel.create filename

let get_out_channel = function
  | None -> Out_channel.stdout
  | Some filename -> Out_channel.create filename

let start_logging_to ~msg logfile =
  match logfile with
   | Some logfile -> Log.enable ~msg logfile
   | _ -> ()

let parse s : string = 
  let lexbuf = Lexing.from_string s in
  let ast = UserFunParser.main UserFunLexer.token lexbuf in
  ast

let gen_user_functions userFs varList : (string*string) list = 
  let flattenVars = (fun (s,t) res -> "(" ^ s ^ " " ^ string_of_typ t ^ ") " ^ res) in
  let varString = "( " ^ (Core.List.fold_right varList flattenVars "") ^ ")" in
  let rec g_u_f userFs iter acc =
    (match userFs with
      | [] -> acc
      | f :: restFs -> 
          let parsedF = parse f in
          let fname = "f_" ^ (string_of_int iter) in
          let z3func = "(define-fun " ^ fname ^ " " ^ varString ^ " Bool " ^ parsedF ^ ")" in
          g_u_f restFs (iter + 1) ((z3func, fname) :: acc))
  in g_u_f userFs 0 []



