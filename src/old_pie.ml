exception BadCounterExample

let good_tests = ref 0
let conflict_counter = ref 0
let record_file = ref ""

let increment_record filename =
    (if Sys.file_exists filename then () else
        let oc = open_out filename in (
            output_string oc "0\n";
            close_out oc));
    let ic = open_in filename in
        let value = int_of_string (input_line ic) in (
            close_in ic;
            let oc = open_out filename in (
                output_string oc ((string_of_int (value + 1)) ^ "\n");
                close_out oc))

let hash_of_list l = BatHashtbl.of_enum(BatList.enum l)

  



    
(* PAC Learning Specifications *)

 (* cnfopt has type string cnf option
  * post has type string
  * *)
let print_spec chan (cnfopt, post) =
  match cnfopt with
      None -> output_string chan ("features are insufficient to separate positive and negative examples for postcondition " ^ post ^ "\n")
    | Some cnf ->
        output_string chan ("precondition: " ^ (string_of_cnf cnf) ^ "\n");
        output_string chan ("postcondition: " ^ post ^ "\n")

let print_specs chan specs =
  BatList.iter (fun s -> (output_string chan "\n"); (print_spec chan s); output_string chan "\n") specs


exception Ambiguous_test of value list


let synthFeatures ?(fname="") ?(consts=[]) ?(comps=[]) ?(arg_names=[]) (f : 'a -> 'b)
                  (missing_features : ('a * ('b, exn) BatResult.t * (int * bool) list * bool) list)
                  (postcond: ('a -> 'b result -> bool) * 'c) (trans: typ list * ('a -> value list))
                  : (('a -> bool) * 'c) list =

    if missing_features = [] then []
    else (
        if fname = "" then () else (
          let conflict_log = open_out (fname ^ "." ^ (string_of_int !conflict_counter) ^ ".con") in
            output_string conflict_log "\nData::\n";
            List.iter (fun (d,_,_,b) -> output_string conflict_log ((string_of_bool b) ^ " <= ");
                                        print_data conflict_log (VList ((snd trans) d));
                                        output_string conflict_log "\n")
                      missing_features;
            close_out(conflict_log));
        let tab = BatHashtbl.create (List.length missing_features) in
            BatList.iter (fun (i, _, _, b) ->
              try (if (BatHashtbl.find tab ((snd trans) i)) <> (VBool b) then raise (Ambiguous_test ((snd trans) i)))
              with Not_found -> BatHashtbl.add tab ((snd trans) i) (VBool b)) missing_features;
            prerr_string "\r    [%] Removing conflicts ... "; flush_all();
            let xtask = {
                target = {
                    domain = (fst trans);
                    codomain = TBool;
                    apply = (fun t -> try BatHashtbl.find tab t with _ -> VDontCare);
                    name = "synth";
                    dump = _unsupported_
                };
                inputs = BatList.mapi (fun i _ ->
                    ((if arg_names = []
                      then ((("x" ^ (string_of_int i) ^ "g"), (fun ars -> List.nth ars i)),
                            Leaf ("x" ^ (string_of_int i) ^ "g"))
                      else (((List.nth arg_names i), (fun ars -> List.nth ars i)),
                            Leaf (List.nth arg_names i))),
                    Array.of_list (BatHashtbl.fold (fun k _ acc -> (List.nth k i)::acc) tab []))) (fst trans);
                components = default_int @ default_string @ default_bool @ comps
            } in
            let solutions = solve xtask consts in
              prerr_string ("(" ^ (string_of_int (!synth_candidates)) ^ " explored)\n"); flush_all();
              (if fname = "" then () else
                let conflict_log = open_out_gen [Open_append] 0 (fname ^ "." ^ (string_of_int !conflict_counter) ^ ".con") in
                  conflict_counter := !conflict_counter + 1;
                  output_string conflict_log "\nSolutions::\n";
                  List.iter (fun (a,_) -> output_string conflict_log a; output_string conflict_log "\n") solutions;
                  close_out conflict_log;);
              (if !record_file = "" then () else increment_record (!record_file ^ ".escher"));
              List.map (fun (annot, func) -> (fun data -> (func (snd trans) data) = VBool true), annot) solutions)


(* default conflict group size *)
let max_conflict_set_size = ref 16
let resolveConflict ?(fname="") ?(consts=[]) ?(comps=[]) ?(arg_names=[]) (f : 'a -> 'b)
                    (missing_features : ('a * ('b, exn) BatResult.t * (int * bool) list * bool) list)
                    (postcond: ('a -> 'b result -> bool) * 'c) (trans: typ list * ('a -> value list))
                    : (('a -> bool) * 'c) list =

    let final_mfs = if List.length missing_features < !max_conflict_set_size then missing_features else
        (let (good_mfs, bad_mfs) =
            List.fold_left (fun (g,b) mf -> match mf with (_,_,_,p) -> if p then ((mf::g),b) else (g,(mf::b)))
                           ([],[]) missing_features in
            let final_good_mfs = BatList.take (!max_conflict_set_size / 2) good_mfs in
            let final_bad_mfs = BatList.take (!max_conflict_set_size / 2) bad_mfs in
                final_good_mfs @ final_bad_mfs) in
        synthFeatures ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f final_mfs postcond trans


(* try to resolve the first group of conflicting tests that can be resolved *)
let rec convergeOneMissingFeature ?(fname="") ?(consts=[]) ?(comps=[]) ?(arg_names=[]) (f: 'a -> 'b)
                                  (missing_features: ('a * ('b, exn) BatResult.t * (int * bool) list * bool) list list)
                                  (postcond: ('a -> 'b result -> bool) * 'c) (trans: typ list * ('a -> value list))
                                  : (('a -> bool) * 'c) list =

    if missing_features = [] then []
    else let new_features = resolveConflict ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f (List.hd missing_features) postcond trans
            in if not (new_features = []) then new_features
            else convergeOneMissingFeature ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f (List.tl missing_features) postcond trans


(* try to resolve all groups of conflicting tests for one post condition*)
  let rec convergePCondFeatures ?(fname="") ?(consts=[]) ?(comps=[]) ?(arg_names=[]) (f: 'a -> 'b) (tests : 'a list)
                                (features: (('a -> bool) * 'c) list) (postcond: ('a -> 'b result -> bool) * 'c)
                                (trans: typ list * ('a -> value list)) :(('a -> bool) * 'c) list =

    let all_missing_features = missingFeatures f tests features postcond in
        if all_missing_features = []
        then features
        else let mf = convergeOneMissingFeature ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f all_missing_features postcond trans
             in if mf = [] then features else convergePCondFeatures ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f tests (features @ mf) postcond trans



let resolveAndPacLearnSpec ?(k=1) ?(dump=("", (fun a -> ""))) ?(record="") ?(consts=[]) ?(comps=[])
                           ?(arg_names=[]) (f: 'a -> 'b) (tests: 'a list)
                           (features : (('a -> bool) * 'c) list) (posts : (('a -> 'b result -> bool) * 'c) list)
                           (trans : typ list * ('a -> value list)) : ('c cnf option * 'c) list =

  record_file := record;
  if fst dump = "" then () else (
    conflict_counter := 0;
    Sys.command("rm -rf " ^ (fst dump) ^ ".*.con");
    let test_file = open_out ((fst dump) ^ ".tests") in
      List.iter (fun t -> output_string test_file (((snd dump) t) ^ "\n")) tests;
      close_out test_file);

  List.map (fun post ->
    (* remove all tests which throw IgnoreTest *)
    let tests = (List.fold_left (fun p t -> try (fst post) t (BatResult.catch f t) ; (t::p) with IgnoreTest -> p) [] tests) in (
      let res = pacLearnSpecIncrK ~k:k f tests
                                  (if fst trans = [] then features
                                   else convergePCondFeatures ~fname:(fst dump) ~consts:consts ~comps:comps
                                                              ~arg_names:arg_names f tests features post trans)
                                  post in
        ((* output_string stderr "\n" ; print_spec stderr res ; *) res)
    )) posts

let rec pacLearnSpecAndVerify ?(k=1) ?(dump=("", (fun a -> ""))) ?(record="") ?(consts=[]) ?(unsats=[])
                              ?(comps=[]) (f : 'a -> 'b) (tests : 'a list) (features : (('a -> bool) * 'c) list)
                              (post : ('a -> 'b result -> bool) * 'c) (trans : typ list * ('a -> value list))
                              (trans_test: 'z -> 'a) (smtfile : string): 'c cnf option =

    (* We would never have IgnoreTest exception in this case *)

  (if (!good_tests < 1) then (good_tests := List.length tests) else ());
  record_file := record;
  (if fst dump = "" then () else (
    conflict_counter := 0;
    Sys.command("rm -rf " ^ (fst dump) ^ ".*.con");
    let test_file = open_out ((fst dump) ^ ".tests") in
      List.iter (fun t -> output_string test_file (((snd dump) t) ^ "\n")) tests;
      close_out test_file));

  let rec helper k unsats tests features = (
    let features =
      if fst trans = [] then features
      else (try convergePCondFeatures ~fname:(fst dump) ~consts:consts ~comps:comps f tests features post trans
            with Ambiguous_test(value_list) ->
              let ambiguous_out = open_out("ambiguous") in
              print_data ambiguous_out (VList(value_list));
              close_out ambiguous_out; [])
    in

    if missingFeatures f tests features post <> [] then None else (
      let res = fst (pacLearnSpec ~k:k f ~tests:tests ~features:features post) in
      if res = None then (
        helper (k + 1) unsats tests features
      ) else (
        let our_output = open_out (smtfile ^ ".xour") in
          print_cnf our_output res ;
          close_out our_output ;
          Sys.command ("./var_replace " ^ smtfile ^ ".tml < " ^ smtfile ^ ".xour > " ^ smtfile ^ ".your") ;
          prerr_string ("\r    [?] Verifying [k = " ^ (string_of_int k) ^ "] --- ");
          let candidate = open_in (smtfile ^ ".your") in (prerr_string (input_line candidate) ; close_in candidate);
          prerr_string "                            \n" ; flush_all();
          Sys.command ("./verify " ^ smtfile ^ ".your " ^ smtfile ^ " 1 0 " ^ !record_file ^ " > " ^ smtfile ^ ".zour") ;
          let res_file = open_in (smtfile ^ ".zour") in
            if input_line res_file = "UNSAT" then (close_in res_file ; res)
            else (close_in res_file ;
                  Sys.command("./var_replace revVals " ^ smtfile ^ ".tml < " ^ smtfile ^ ".zour > " ^ smtfile ^ ".our") ;
                  let res_file = open_in (smtfile ^ ".our") in
                  let args = (List.map (fun vtyp -> let data = input_line res_file in match vtyp with TInt -> VInt(int_of_string data) | TString -> VString(data)) (fst trans)) in
                  prerr_string "      [+] Added test ... "; print_data stderr (VList(args)); prerr_string "\n";
                  close_in res_file;
                  if f (trans_test args) then raise BadCounterExample else (helper 1 unsats ((trans_test args) :: tests) features)))))
  in helper k unsats tests features