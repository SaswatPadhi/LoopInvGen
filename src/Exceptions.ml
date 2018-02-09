exception Parse_Exn of string
exception Internal_Exn of string
exception Illegal_Call_Exn of string
exception Invalid_Type_Exn of string
exception False_Pre_Exn of string
exception Ambiguous_Test of string
exception Duplicate_Test of string

(* thrown if there is no boolean function consistent with the given
   positive and negative examples. Possible in two situations:
     > a positive and negative example have the identical feature vector
     > there is no k-CNF formula (for some particular k being used)
       that distinguishes the positive and negative examples
*)
exception NoSuchFunction
exception ClauseEncodingError

(* a postcondition should raise this exception to indicate
   that the given test input should be ignored *)
exception IgnoreTest