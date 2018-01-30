open Types

type component = {
  name : string ;
  codomain : typ ;
  domain : typ list ;
  check : program list -> bool ;
  apply : value list -> value ;
  dump : string list -> string ;
}