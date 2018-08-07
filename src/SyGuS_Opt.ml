open Core_kernel
open Sexplib

open Exceptions
open SyGuS
open Utils

module Bitarray = Core_extended.Bitarray

(* * *
 * Optimization / Simplification of a SyGuS-INV problem:
 * -------------------------------------------------------
 * We preserve all functions and all arguments to functions.
 * However, we reduce the [synth_variables], i.e. the variables
 * over which to synthesize invariants.
 * The assumption is that, having additional unused functions
 * and variables should incur negligible overhead if they are
 * ultimately unconstrained.
 * * *)

type func_info
 = { callees : string list
   ; used_args : Bitarray.t
   ; parsed_expr : Sexp.t
   ; caller : func }

(* FIXME: SyGuS format allows overloaded functions with different signatures *)
let make_call_table (sygus : t) : func_info String.Table.t =
  let rec extract_operators (exp : Sexp.t) : string list =
    match exp with
    | List((Atom op) :: op_args)
      -> op :: (List.fold op_args ~init:[] ~f:(fun acc arg -> acc @ (extract_operators arg)))
    | _ -> []
  in let init_info f = { caller = f
                       ; parsed_expr = Atom ""
                       ; callees = []
                       ; used_args = Bitarray.create (List.length f.args) }
  in let table = String.Table.create () ~size:(List.length sygus.functions) ~growth_allowed:false
      in List.iter sygus.functions ~f:(fun func -> String.Table.set table ~key:func.name ~data:(init_info func))
       ; List.iter sygus.functions ~f:(fun func ->
           let parsed_expr = Parsexp.Single.parse_string_exn func.expr in
           let ops =  extract_operators parsed_expr in
           let callees = List.filter ops ~f:(fun op -> String.Table.find table op <> None)
            in String.Table.update table func.name
                                   ~f:(fun [@warning "-8"] (Some data) -> {data with callees ; parsed_expr}))
       ; String.Table.update table sygus.post_func.name
                             ~f:(fun [@warning "-8"] (Some data)
                                   -> {data with callees = sygus.pre_func.name :: sygus.trans_func.name :: data.callees})
       ; table

let toposort_funcs (root_func_name : string) (call_table : func_info String.Table.t) : string list =
  let rec sort path visited = function
    | [] -> visited
    | n::nodes -> if List.mem ~equal:String.equal path n
                  then raise (Parse_Exn "Cyclic dependency within functions!")
                  else let v' = if List.mem ~equal:String.equal visited n then visited
                                else n :: (sort (n::path) visited (String.Table.find_exn call_table n).callees)
                        in sort path v' nodes
   in sort [] [] [root_func_name]

let update_used_args (call_table : func_info String.Table.t) (func_name : string) : unit
 = let data = String.Table.find_exn call_table func_name in
   let rec check_args = let open Sexp in function
     | (Atom a) | List([Atom a])
       -> begin match List.findi data.caller.args ~f:(fun _ (v, _) -> String.equal v a ) with
          | None -> ()
          | Some (i, _) -> Bitarray.set data.used_args i true
          end
     | List((Atom op) :: op_args)
       ->  begin match String.Table.find call_table op with
           | None -> List.iter op_args ~f:check_args
           | Some callee_data -> List.iteri op_args ~f:(fun i arg -> if Bitarray.get callee_data.used_args i then check_args arg)
           end
     | _ -> ()
   in check_args data.parsed_expr

let optimize (sygus : t) : t =
  let call_table = make_call_table sygus in
  let get_used_vars fname
      = let data = String.Table.find_exn call_table fname
         in List.filter_mapi data.caller.args ~f:(fun i v -> if Bitarray.get data.used_args i then Some v else None)
  in let ts_funcs = toposort_funcs sygus.post_func.name call_table
  in Log.debug (lazy ("Initial synth variables: " ^ (List.to_string_map sygus.synth_variables ~sep:"; " ~f:fst)))
   ; Log.debug (lazy ("Topological sort of functions: " ^ (String.concat ~sep:"; " ts_funcs)))
   ; List.(iter (rev ts_funcs) ~f:(update_used_args call_table))
   ; Log.debug (lazy (String.Table.fold call_table ~init:"Used function arguments:"
                        ~f:(fun ~key ~data s -> s ^ (Log.indented_sep 2) ^ key ^ " -> "
                                              ^ (String.concat ~sep:"; "
                                                   (List.filter_mapi data.caller.args
                                                      ~f:(fun i (v, _) -> if Bitarray.get data.used_args i
                                                                          then Some v else None))))))
   ; let sygus = { sygus with
                   synth_variables = List.dedup_and_sort ~compare:Poly.compare
                                       ((get_used_vars sygus.pre_func.name)
                                       @ (List.map (get_used_vars sygus.trans_func.name)
                                                   ~f:(fun (v, t) -> match String.chop_suffix ~suffix:"!" v with
                                                                     | None -> (v, t)
                                                                     | Some v' -> (v', t)))
                                       @ (get_used_vars sygus.post_func.name))
                 }
      in Log.debug (lazy ("Reduced synth variables: " ^ (List.to_string_map sygus.synth_variables ~sep:"; " ~f:fst)))
       ; sygus