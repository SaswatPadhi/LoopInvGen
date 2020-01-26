open Base

open LoopInvGen

let bveq_eval = (List.find_exn BitVecComponents.all
                    ~f:(fun comp -> String.equal comp.name "bv-eq")).evaluate
let bvadd_eval = (List.find_exn BitVecComponents.all
                    ~f:(fun comp -> String.equal comp.name "bvadd")).evaluate
let bvnot_eval = (List.find_exn BitVecComponents.all
                    ~f:(fun comp -> String.equal comp.name "bvnot")).evaluate
let bvult_eval = (List.find_exn BitVecComponents.all
                    ~f:(fun comp -> String.equal comp.name "bvult")).evaluate
let bvuge_eval = (List.find_exn BitVecComponents.all
                    ~f:(fun comp -> String.equal comp.name "bvuge")).evaluate
let bvugt_eval = (List.find_exn BitVecComponents.all
                    ~f:(fun comp -> String.equal comp.name "bvugt")).evaluate
let bvule_eval = (List.find_exn BitVecComponents.all
                    ~f:(fun comp -> String.equal comp.name "bvule")).evaluate
let bvsub_eval = (List.find_exn BitVecComponents.all
                    ~f:(fun comp -> String.equal comp.name "bvsub")).evaluate


let equal_hex_bin () =
  let bv1 = Value.BitVec (Bitarray.of_string "#x1010") in
  let bv2 = Value.BitVec (Bitarray.of_string "#b0001000000010000") in
  let eq_ret = bveq_eval [bv1; bv2] in
  let ret = Value.equal (Value.Bool true) eq_ret in
  Alcotest.(check bool) "identical" true ret

let bvadd () =
  let bv1 = Value.BitVec (Bitarray.of_string "#b10101010101010101") in
  let bv2 = Value.BitVec (Bitarray.of_string "#b01010101010101010") in
  let add_ret = bvadd_eval [bv1; bv2] in
  let ret = Value.equal (Value.BitVec (Bitarray.of_string "#b11111111111111111")) add_ret in
  Alcotest.(check bool) "identical" true ret

let bvadd_ovf () =
  let bv1 = Value.BitVec (Bitarray.of_string "#b10101010101010101") in
  let bv2 = Value.BitVec (Bitarray.of_string "#b01010101010101011") in
  let add_ret = bvadd_eval [bv1; bv2] in
  let ret = Value.equal (Value.BitVec (Bitarray.of_string "#b00000000000000000")) add_ret in
  Alcotest.(check bool) "identical" true ret  

let bvnot () =
  let bv = Value.BitVec (Bitarray.of_string "#xa482ad9301") in
  let bvnot_ret = bvnot_eval [bv] in
  let ret = Value.equal (Value.BitVec (Bitarray.of_string "#x5b7d526cfe")) bvnot_ret in
  Alcotest.(check bool) "identical" true ret

let bvult_same () =
  let bv1 = Value.BitVec (Bitarray.of_string "#x00000000") in
  let bvult_ret = bvult_eval [bv1; bv1] in
  let ret = Value.equal (Value.Bool false) bvult_ret in
  Alcotest.(check bool) "identical" true ret

let bvult_ovf () =
  (* bv1 is a bitvector which has a 63bit Bitarray *)
  let bv1 = Value.BitVec
              (Bitarray.of_string
                 "#b111111111111111111111111111111111111111111111111111111111111111") in
  let bvult_ret = bvult_eval [bv1; bv1] in
  let ret = Value.equal (Value.Bool false) bvult_ret in
  Alcotest.(check bool) "identical" true ret

let bvult_onegreater () =
  let bv1 = Value.BitVec (Bitarray.of_string "#x1") in
  let bv2 = Value.BitVec (Bitarray.of_string "#x0") in  
  let bvult_ret = bvult_eval [bv2; bv1] in
  let ret = Value.equal (Value.Bool true) bvult_ret in
  Alcotest.(check bool) "identical" true ret

let bvuge () =
  let bv1 = Value.BitVec (Bitarray.of_string "#xff") in
  let bv2 = Value.BitVec (Bitarray.of_string "#b11111111") in  
  let bvuge_ret = bvuge_eval [bv2; bv1] in
  let ret = Value.equal (Value.Bool true) bvuge_ret in
  Alcotest.(check bool) "identical" true ret
  
let bvugt () =
  let bv1 = Value.BitVec (Bitarray.of_string "#xa") in
  let bv2 = Value.BitVec (Bitarray.of_string "#b1000") in  
  let bvugt_ret = bvugt_eval [bv1; bv2] in
  let ret = Value.equal (Value.Bool true) bvugt_ret in
  Alcotest.(check bool) "identical" true ret

let bvule () =
  let bv1 = Value.BitVec (Bitarray.of_string "#x1") in
  let bv2 = Value.BitVec (Bitarray.of_string "#xb") in  
  let bvule_ret = bvult_eval [bv1; bv2] in
  let ret = Value.equal (Value.Bool true) bvule_ret in
  Alcotest.(check bool) "identical" true ret

let bvsub () =
  let bv1 = Value.BitVec (Bitarray.of_string "#b00") in
  let bv2 = Value.BitVec (Bitarray.of_string "#b01") in  
  let bvsub_ret = bvsub_eval [bv1; bv2] in
  (* We should get the representation for -1 *)
  let ret = Value.equal (Value.BitVec (Bitarray.of_string "#b11")) bvsub_ret in
  Alcotest.(check bool) "identical" true ret


let bv_pp f p = match p with
  | Value.BitVec ba -> Format.fprintf f "%s\n" (Bitarray.to_string ba)
  | _ -> Format.fprintf f "Error with pretty printing the BitVector\n"
            
let bitvec_testable = Alcotest.testable bv_pp (fun x y -> Value.equal (Value.Bool true) (bveq_eval [x; y]))

let gen () =                                     
  let bvgen1 = TestGen.for_type (Type.BITVEC (Type.TVAR "32")) in
  let bvgen2 = TestGen.for_type (Type.BITVEC (Type.TVAR "32")) in
  Alcotest.(check (neg bitvec_testable)) "identical"
    (Core.Quickcheck.Generator.generate bvgen1 ~size:1 ~random:(Splittable_random.State.of_int 1))
    (Core.Quickcheck.Generator.generate bvgen2 ~size:1 ~random:(Splittable_random.State.of_int 2))
  
  
let all = [
    "equal hex and binary", `Quick, equal_hex_bin ;
    "bvadd", `Quick, bvadd ;
    "bvadd_ovf", `Quick, bvadd_ovf ;
    "bvnot", `Quick, bvnot ;
    "bvult_same", `Quick, bvult_same ;
    "bvult_ovf", `Quick, bvult_ovf ;
    "bvult_onegreater", `Quick, bvult_onegreater ;
    "bvuge", `Quick, bvuge ;
    "bvugt", `Quick, bvugt ;
    "bvule", `Quick, bvule ;
    "bvsub", `Quick, bvsub ;
    "gen", `Quick, gen
  ]
                   
