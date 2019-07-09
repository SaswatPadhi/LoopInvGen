open Core_kernel

type t = {
  name : string ;
  components_per_level : Expr.component list array ;
  sample_set_size_multiplier : int
}

let all_supported =  
   let table = String.Table.create () ~size:2
   in List.iter ~f:(fun component -> String.Table.set table ~key:component.name ~data:component)
        [{
           name = "LIA" ;
           components_per_level = [|
             (BooleanComponents.all @ IntegerComponents.equality) ;
             (BooleanComponents.all @ IntegerComponents.intervals) ;
             (BooleanComponents.all @ IntegerComponents.octagons) ;
             (BooleanComponents.all @ IntegerComponents.polyhedra) ;
           |] ;
           sample_set_size_multiplier = 1
         } ; {
           name = "NIA" ;
           components_per_level = [|
             (BooleanComponents.all @ IntegerComponents.equality) ;
             (BooleanComponents.all @ IntegerComponents.intervals) ;
             (BooleanComponents.all @ IntegerComponents.octagons) ;
             (BooleanComponents.all @ IntegerComponents.polyhedra) ;
             (BooleanComponents.all @ IntegerComponents.polynomials) ;
             (BooleanComponents.all @ IntegerComponents.peano) ;
           |] ;
           sample_set_size_multiplier = 8
         } ; {
          name = "ALIA" ;
          components_per_level = [|
            (BooleanComponents.all @ IntegerComponents.equality @ ArrayComponents.all) ;
            (BooleanComponents.all @ IntegerComponents.intervals) ;
            (BooleanComponents.all @ IntegerComponents.octagons) ;
            (BooleanComponents.all @ IntegerComponents.polyhedra) ;
          |] ;
          sample_set_size_multiplier = 1
        }]
    ; table

let of_string name = String.Table.find_exn all_supported name
