open Core_kernel

type t = {
  name : string ;
  components_per_level : Expr.component list array ;
  sample_set_size_multiplier : int
}

let ( *** ) = fun x y ->
  Array.(map ~f:(fun (ex,ey) -> ex @ ey) (cartesian_product x y))

let all_supported =
   let table = String.Table.create () ~size:2
   in List.iter ~f:(fun component -> String.Table.set table ~key:component.name ~data:component)
        [{
           name = "LIA" ;
           components_per_level = BooleanComponents.levels *** IntegerComponents.linear_levels ;
           sample_set_size_multiplier = 1
         } ; {
           name = "NIA" ;
           components_per_level = BooleanComponents.levels *** IntegerComponents.non_linear_levels ;
           sample_set_size_multiplier = 8
         } ; {
           name = "ALIA" ;
           (* FIXME: Determine levels of ArrayComponents for hybrid enumeration *)
           components_per_level = ArrayComponents.levels *** BooleanComponents.levels *** IntegerComponents.linear_levels ;
           sample_set_size_multiplier = 1
         } ; {
           name = "ANIA" ;
           (* FIXME: Determine levels of ArrayComponents for hybrid enumeration *)
           components_per_level = ArrayComponents.levels *** BooleanComponents.levels *** IntegerComponents.non_linear_levels ;
           sample_set_size_multiplier = 8
        }]
    ; table

let of_string name = String.Table.find_exn all_supported name