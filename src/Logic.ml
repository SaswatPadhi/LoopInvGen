open Core_kernel

type t = {
  name : string ;
  components : Expr.component list ;
  conflict_group_size_multiplier : int
}

let all_supported =
  let table = String.Table.create () ~size:2 in
  let is (with_name : string) (component : Expr.component)
      = String.equal component.name with_name
  let except (with_name : string) (component : Expr.component)
      = not (is with_name component)
   in List.iter ~f:(fun component -> String.Table.set table ~key:component.name ~data:component)
        [{
           name = "LIA" ;
           components = (List.filter Th_LIA.components ~f:(except "lin-int-mult"))
                      @ Th_Bool.components ;
           conflict_group_size_multiplier = 1
         } ; {
           name = "NIA" ;
           components =  (List.hd_exn Th_LIA.components)
                      :: (List.find Th_NIA.components ~f:(is "nonlin-int-mult"))
                      :: (List.tl_exn (List.tl_exn Th_LIA.components))
                      :: (List.filter Th_NIA.components ~f:(except "nonlin-int-mult"))
                      @ Th_Bool.components ;
           conflict_group_size_multiplier = 2
         }]
    ; table

let of_string name = String.Table.find_exn all_supported name
