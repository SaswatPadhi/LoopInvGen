open Core_kernel

type t = {
  name : string ;
  components : Expr.component list ;
  conflict_group_size_multiplier : int
}

let all_supported =
  let table = String.Table.create () ~size:2 in
  let except (with_name : string) (component : Expr.component)
      = not (String.equal component.name with_name)
   in List.iter ~f:(fun component -> String.Table.set table ~key:component.name ~data:component)
        [{
           name = "LIA" ;
           components = Th_Bool.components @ Th_LIA.components ;
           conflict_group_size_multiplier = 1
         } ; {
           name = "NIA" ;
           components = Th_Bool.components
                      @ (List.filter Th_LIA.components ~f:(except "lin-int-mult"))
                      @ Th_NIA.components ;
           conflict_group_size_multiplier = 2
         }]
    ; table

let of_string name = String.Table.find_exn all_supported name