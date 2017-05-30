open Types

type component = {
  name : string ;
  codomain : typ ;
  domain : typ list ;
  apply : value list -> value ;
  dump : string list -> string ;
}