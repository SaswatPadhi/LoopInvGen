open Core_kernel

open LoopInvGen

let print_PI_results (result, stats) =
  let open PIE in
  Stdio.(Out_channel.output_lines stdout [
    ("The precondition is: " ^ (cnf_opt_to_desc result)) ;
    ("  > Total time (ms): " ^ (Float.to_string stats.pi_time_ms)) ;
    ("  > Synth time (ms): [" ^ (Utils.List.to_string_map
                                    ~sep:"; " stats._Synthesizer
                                    ~f:(fun s -> Float.to_string (s.synth_time_ms)))
                              ^ "]") ;
    ""
  ])

(* a job for inferring a precondition to ensure that the absolute value`
   function has a result equal to its argument *)
let abs_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (if x > 0 then x else -x))
  ~args:([ ("x", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ], Ok (Value.Int y) -> -x = y)
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.INT))))

let with_synth_PI () =
  Stdio.print_endline "PI for { x = abs(x) } with feature learning:" ;
  print_PI_results (PIE.learnPreCond abs_job)

let real_abs_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Real x ] -> Value.Real (if Float.(x > 0.) then x else (-1. *. x)))
  ~args:([ ("x", Type.REAL) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Real x ], Ok (Value.Real y) -> Float.(equal (-1. *. x) y))
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.REAL))))

let real_abs_PI () =
  Stdio.print_endline "PI for { x = abs(x) } with feature learning:" ;
  print_PI_results (
    PIE.learnPreCond real_abs_job
    ~config:PIE.Config.{ default with _Synthesizer = { default._Synthesizer with logic = Logic.of_string "ALL" } }
    )


let real_prod_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Real x ] -> Value.Real ( x *. x))
  ~args:([ ("x", Type.REAL) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Real x ], Ok (Value.Real y) -> Float.( Float.(y > x)))
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.REAL))))

let real_prod_PI () =
  Stdio.print_endline "PI for { x = x*x } with feature learning:" ;
  print_PI_results (PIE.learnPreCond real_prod_job
      ~config:PIE.Config.{ default with _Synthesizer = { default._Synthesizer with logic = Logic.of_string "ALL" } }
    )

let append_job =
  
  Job.create_unlabeled
    ~f:(fun [@warning "-8"] [ List (INT, x) ; List (INT, y) ]
        -> List (INT, (x @ y)))
    ~args:([ ("x", Type.(LIST INT)) ; ("y", Type.(LIST INT)) ])
    ~post:(fun inp res ->
            match [@warning "-8"] inp , res with
            | [ List (_, l1) ; List (_, l2) ] , Ok (List (INT, res)) -> List.is_empty res)
    (* We start with these two features and disable feature synthesis *)
    ~features:[
      ((fun [@warning "-8"] [ List (INT, list1) ; _ ] -> List.is_empty list1),
       "(= x [])") ;
      ((fun [@warning "-8"] [ _ ; List (INT, list2) ] -> List.is_empty list2),
       "(= y [])") ;
    ]
    
(List.map ~f:(
  fun (x,y)  -> [x ;y])
  Quickcheck.(random_value
    (Generator.list_with_length 64
       (Generator.tuple2
          (TestGen.for_type (Type.LIST Type.INT))
          (TestGen.for_type (Type.LIST Type.INT))))))





let no_synth_PI () =
  Stdio.print_endline "PI for { append(l1,l2) = [] } without feature learning:" ;
  print_PI_results (
    PIE.learnPreCond append_job
                     ~config:{ PIE.Config.default with disable_synth = true } 
  )

let append_job_2 =
  
  Job.create_unlabeled
    ~f:(fun [@warning "-8"] [ List (INT, x) ; List (INT, y) ]
        -> List (INT, (x @ y)))
    ~args:([ ("x", Type.(LIST INT)) ; ("y", Type.(LIST INT)) ])
    ~post:(fun inp res ->
            match [@warning "-8"] inp , res with
            | [ List (INT, l1) ; List (INT, l2) ] , Ok (List (INT, res)) ->  List.equal Value.equal res l1)
    (* We start with these two features and disable feature synthesis *)
    ~features:[
      ((fun [@warning "-8"] [ List (INT, list1) ; _ ] -> List.is_empty list1),
       "(= x [])") ;
      ((fun [@warning "-8"] [ _ ; List (INT, list2) ] -> List.is_empty list2),
       "(= y [])") ;
    ]
  
    (List.map ~f:(
  fun (x,y)  -> [x ;y])
  Quickcheck.(random_value
    (Generator.list_with_length 512
       (Generator.tuple2
          (TestGen.for_type (Type.LIST Type.INT))
          (TestGen.for_type (Type.LIST Type.INT))))))

let no_synth_PI_2 () =
  Stdio.print_endline "PI for { append(l1,l2) = [] } without feature learning:" ;
  print_PI_results (
    PIE.learnPreCond append_job_2
                     ~config:{ PIE.Config.default with disable_synth = true } 
  )

  let append_job_3 =
  
  Job.create_unlabeled
    ~f:(fun [@warning "-8"] [ List (INT, x) ; List (INT, y) ]
        -> List (INT, (x @ y)))
    ~args:([ ("x", Type.(LIST INT)) ; ("y", Type.(LIST INT)) ])
    ~post:(fun inp res ->
            match [@warning "-8"] inp , res with
            | [ List (INT, l1) ; List (INT, l2) ] , Ok (List (INT, res)) -> (List.length res) = 2)
    (* We start with these two features and disable feature synthesis *)
   ~features:[
      ((fun [@warning "-8"] [ List (INT, list1) ; _ ] -> List.is_empty list1),
       "(= x [])") ;
      ((fun [@warning "-8"] [ _ ; List (INT, list2) ] -> List.is_empty list2),
       "(= y [])") ;
    ]


     (List.map ~f:(
  fun (x,y)  -> [x ;y])
  Quickcheck.(random_value
    (Generator.list_with_length 4096
       (Generator.tuple2
          (TestGen.for_type (Type.LIST Type.INT))
          (TestGen.for_type (Type.LIST Type.INT))))))  

let no_synth_PI_3 () =
  Stdio.print_endline "PI for { append(l1,l2) = [] } without feature learning:" ;
  print_PI_results (
    PIE.learnPreCond append_job_3
                     ~config:PIE.Config.{ default with _Synthesizer = { default._Synthesizer with logic = Logic.of_string "ALL" } }
  )

let rev_append_job =
  
  Job.create_unlabeled
    ~f:(fun [@warning "-8"] [ List (INT, x) ; List (INT, y) ]
        -> List (INT, (List.rev x @ y)))
    ~args:([ ("x", Type.(LIST INT)) ; ("y", Type.(LIST INT)) ])
    ~post:(fun inp res ->
            match [@warning "-8"] inp , res with
            | [ List (INT, l1) ; List (INT, l2) ] , Ok (List (INT, res)) -> (List.equal Value.equal res (l1 @ l2)))
    (* We start with these two features and disable feature synthesis *)
   ~features:[
      ((fun [@warning "-8"] [ List (INT, list1) ; _ ] -> List.is_empty list1),
       "(= x [])") ;
      ((fun [@warning "-8"] [ _ ; List (INT, list2) ] -> List.is_empty list2),
       "(= y [])") ;
    ]

     (List.map ~f:(
  fun (x,y)  -> [x ;y])
  Quickcheck.(random_value
    (Generator.list_with_length 4096
       (Generator.tuple2
          (TestGen.for_type (Type.LIST Type.INT))
          (TestGen.for_type (Type.LIST Type.INT))))))  

let rev_append_synth_pi () =
  Stdio.print_endline "PI for { rev append(l1,l2) = [] } without feature learning:" ;
  print_PI_results (
    PIE.learnPreCond rev_append_job
                     ~config:PIE.Config.{ default with _Synthesizer = { default._Synthesizer with logic = Logic.of_string "ALL" } }
  )



  let comp_len_job =
  
  Job.create_unlabeled
    ~f:(fun [@warning "-8"] [ List (INT, x) ; List (INT, y) ]
        -> Int (compare( List.length x) (List.length y) ))
    ~args:([ ("x", Type.(LIST INT)) ; ("y", Type.(LIST INT)) ])
    ~post:(fun inp res ->
            match [@warning "-8"] inp , res with
            | [ List (INT, l1) ; List (INT, l2) ] , Ok (Int  res) -> (res = 0))
    (* We start with these two features and disable feature synthesis *)
   ~features:[
      ((fun [@warning "-8"] [ List (INT, list1) ; _ ] -> List.is_empty list1),
       "(= x [])") ;
      ((fun [@warning "-8"] [ _ ; List (INT, list2) ] -> List.is_empty list2),
       "(= y [])") ;
    ]

  (List.map ~f:(
  fun (x,y)  -> [x ;y])
  Quickcheck.(random_value
    (Generator.list_with_length 4096
       (Generator.tuple2
          (TestGen.for_type (Type.LIST Type.INT))
          (TestGen.for_type (Type.LIST Type.INT))))))  

let comp_len_PI () =
  Stdio.print_endline "PI for { compare_lengths l1 l2 = 0 } without feature learning:" ;
  print_PI_results (
    PIE.learnPreCond comp_len_job
                     ~config:PIE.Config.{ default with _Synthesizer = { default._Synthesizer with logic = Logic.of_string "ALL" } }
  )





let square_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (x*x))
  ~args:([ ("x", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ], Ok (Value.Int y) -> y/x = abs(x))
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.INT))))

  let square_synth_pi () =
  Stdio.print_endline "PI for { x = x*x } with feature learning:" ;
  print_PI_results (PIE.learnPreCond square_job)


  

  let cube_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (x*x*x))
  ~args:([ ("x", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ], Ok (Value.Int y) -> 1 < y)
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.INT))))

 let cube_synth_pi () =
  Stdio.print_endline "PI for { x = x*x*x } with feature learning:" ;
  print_PI_results (PIE.learnPreCond cube_job)

let inverse_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (1/x))
  ~args:([ ("x", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ], Ok (Value.Int y) -> -x > y)
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.INT))))

  let inverse_synth_pi () =
  Stdio.print_endline "PI for { x = 1 / x } with feature learning:" ;
  print_PI_results (PIE.learnPreCond inverse_job)

  let even_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int ((x / 2) * 2))
  ~args:([ ("x", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ], Ok (Value.Int y) -> x = y)
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 100
                 (TestGen.for_type Type.INT))))

  let even_synth_pi () =
  Stdio.print_endline "PI for { x = (x / 2) * 2 } with feature learning:" ;
  print_PI_results (PIE.learnPreCond even_job
                                      ~config:{ PIE.Config.default with
              _Synthesizer = { PIE.Config.default._Synthesizer with
                               logic = Logic.of_string "NIA" } }
) 

  let product_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ; Value.Int y] -> Value.Int (x*y))
  ~args:([ ("x", Type.INT) ; ("y", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ; Value.Int y], Ok (Value.Int r) -> r > x)
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.INT))))
  
  let product_synth_pi () =
  Stdio.print_endline "PI for { x = x*y} with feature learning:" ;
  print_PI_results (PIE.learnPreCond product_job)



  let avg_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ; Value.Int y; Value.Int z] -> Value.Int ((x + y + z) / 3))
  ~args:([ ("x", Type.INT) ; ("y", Type.INT) ; ("z", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ; Value.Int y ; Value.Int z], Ok (Value.Int r) -> r = x)
  (* We start with no initial features *)
   ~features:[]
 
  
  (List.map ~f:(fun (x,y,z) -> [ x ; y ; z])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (Generator.tuple3 (TestGen.for_type Type.INT) (TestGen.for_type Type.INT) (TestGen.for_type Type.INT)))))
  
  let avg_synth_pi () =
  Stdio.print_endline "PI for { x = avg(x, y, z)} with feature learning:" ;
  print_PI_results (PIE.learnPreCond avg_job)



  let max_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ; Value.Int y] -> Value.Int (if x > y then x else y))
  ~args:([ ("x", Type.INT) ; ("y", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ; Value.Int y], Ok (Value.Int r) -> r = x && r = y)
  (* We start with no initial features *)
  ~features:[] 
  (List.map ~f:(fun (x,y) -> [ x ; y ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (Generator.tuple2 (TestGen.for_type Type.INT) (TestGen.for_type Type.INT)))))

  let max_synth_pi () =
  Stdio.print_endline "PI for { x = max(x, y)} with feature learning:" ;
  print_PI_results (PIE.learnPreCond max_job)


  
let int_average_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ; Value.Int y] -> Value.Int ((x+y)/2))
  ~args:([ ("x", Type.INT) ; ("y", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ; Value.Int y], Ok (Value.Int r) -> r > x)
  (* We start with no initial features *)
  ~features:[]
  [[Value.Int 1; Value.Int 3]; [Value.Int 4; Value.Int 4]; [Value.Int 5; Value.Int 3] ; [Value.Int 3; Value.Int 5]]
  
  let average_synth_pi () =
  Stdio.print_endline "PI for { x = (x + y) / 2} with feature learning:" ;
  print_PI_results (PIE.learnPreCond int_average_job)

  let int_average_job_2 = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ; Value.Int y] -> Value.Int ((x+y)/2))
  ~args:([ ("x", Type.INT) ; ("y", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ; Value.Int y], Ok (Value.Int r) -> r < x)
  (* We start with no initial features *)
  ~features:[]
  [[Value.Int 1; Value.Int 3]; [Value.Int 4; Value.Int 4]; [Value.Int 5; Value.Int 3] ; [Value.Int 3; Value.Int 5] ; [Value.Int 4; Value.Int 2]]
  
  let average_synth_pi_2 () =
  Stdio.print_endline "PI for { x = (x + y) / 2} with feature learning:" ;
  print_PI_results (PIE.learnPreCond int_average_job_2)

  let int_average_job_3 = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ; Value.Int y] -> Value.Int ((x+y)/2))
  ~args:([ ("x", Type.INT) ; ("y", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ; Value.Int y], Ok (Value.Int r) -> r = x)
  (* We start with no initial features *)
  ~features:[]
  [[Value.Int 1; Value.Int 3]; [Value.Int 4; Value.Int 4]; [Value.Int 5; Value.Int 3] ; [Value.Int 3; Value.Int 5] ; [Value.Int 4; Value.Int 2]]
  
  let average_synth_pi_3 () =
  Stdio.print_endline "PI for { x = (x + y) / 2} with feature learning:" ;
  print_PI_results (PIE.learnPreCond int_average_job_3)



  

let () = with_synth_PI ()
       ; real_abs_PI ()
       ; real_prod_PI ()
       ; no_synth_PI ()
       ; no_synth_PI_2 () 
       ; no_synth_PI_3 () 
       ; rev_append_synth_pi ()
       ; comp_len_PI ()
       ; square_synth_pi ()
       ; cube_synth_pi ()
       ; inverse_synth_pi ()
       ; product_synth_pi ()
       ; max_synth_pi ()
       ; average_synth_pi ()
       ; average_synth_pi_2 ()
       ; average_synth_pi_3 () 
       ; even_synth_pi () 
       ; avg_synth_pi ()
       
     
