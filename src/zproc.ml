open Core
open Core.Unix
open Exceptions
open Sexplib

type proc_info = {
  pid    : Pid.t ;
  stdin  : Out_channel.t ;
  stdout : In_channel.t ;
  stderr : In_channel.t ;
}

let create () : proc_info =
  let open Process_info in
  let pi = create_process "./_dep/z3.bin" ["-in"] in
    Log.info (lazy ("Created z3 instance. PID = " ^ (Pid.to_string pi.pid))) ;
    {
      pid    = pi.pid ;
      stdin  = out_channel_of_descr pi.stdin ;
      stdout = in_channel_of_descr pi.stdout ;
      stderr = in_channel_of_descr pi.stdout ;
    }

let close pi =
  Out_channel.close pi.stdin ; ignore (waitpid pi.pid) ;
  Log.info (lazy ("Closed z3 instance. PID = " ^ (Pid.to_string pi.pid)))

let flush_and_collect (pi : proc_info) : string =
  Out_channel.output_string pi.stdin "()\n" ; Out_channel.flush pi.stdin ;
  let read_string = ref "" in
  let error_line l = ((String.prefix l 12) = "(error \"line" &&
                      (String.suffix l 36) = ": invalid command, symbol expected\")") in
  let rec read_line () : unit =
    match In_channel.input_line pi.stdout with
    | None -> raise (Internal_Exn ("Unexpected termination of z3 channels."))
    | Some l when error_line l -> ()
    | Some l -> read_string := (!read_string) ^ l ; read_line ()
  in read_line () ; !read_string

let run_queries ?local:(local=true) (pi : proc_info)
                (database : string list) (queries : string list) : string list =
  (*Out_channel.output_lines Out_channel.stdout queries ;*)
  if queries = []
  then begin
    if local then () else
      Out_channel.output_lines pi.stdin database ;
      Out_channel.flush pi.stdin ; [""]
    end
  else begin
    let results = ref [] in
      (if local then Out_channel.output_string pi.stdin "(push)\n" else ()) ;
      Out_channel.output_lines pi.stdin database ;
      List.iter queries ~f:(fun q ->
        Out_channel.output_string pi.stdin q ;
        Out_channel.newline pi.stdin ;
        results := (flush_and_collect pi) :: (!results)
      ) ;
      (if local then Out_channel.output_string pi.stdin "(pop)\n" else ()) ;
      Out_channel.flush pi.stdin ; List.rev (!results)
  end

let z3_sexp_to_value (sexp : Sexp.t) : Types.value =
  let open Sexp in
  let unexpected_exn = Internal_Exn ("Unexpected z3 value: " ^ (to_string_hum sexp)) in
  let vstr = match sexp with
             | Atom v -> v
             | List([(Atom "-") ; (Atom v)]) -> "-" ^ v
             | _ -> raise unexpected_exn
  in match Types.deserialize_value vstr with
     | None -> raise unexpected_exn
     | Some v -> v

let z3_result_to_values (result : string) : (string * Types.value) list =
  let open Sexp in
  let unexpected_exn = Internal_Exn ("Unexpected z3 model: " ^ result) in
  match (Sexp.of_string result) with
  | List(Atom("model") :: varexps)
    -> let open List in
       map varexps ~f:(function
                       | List(l) -> begin match (nth_exn l 1) , (nth_exn l 4) with
                                     | (Atom n, v) -> (n, (z3_sexp_to_value v))
                                     | _ -> raise unexpected_exn
                                     end
                       | _ -> raise unexpected_exn)
  | _ -> raise unexpected_exn