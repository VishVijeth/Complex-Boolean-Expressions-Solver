open Proj2_types;;

let buildParseTree (input : string list) : tree = raise (Invalid_argument "Not implemented");;

let buildAbstractSyntaxTree (input : tree) : tree = raise (Invalid_argument "Not implemented");;

let scanVariable (input : string list) : string list = raise (Invalid_argument "Not implemented");;

let generateInitialAssignList (varList : string list) : (string * bool) list = raise (Invalid_argument "Not implemented");;

let generateNextAssignList (assignList : (string * bool) list) : (string * bool) list * bool = raise (Invalid_argument "Not implemented");;

let lookupVar (assignList : (string * bool) list) (str : string) : bool = raise (Invalid_argument "Not implemented");;

let evaluateTree (t : tree) (assignList : (string * bool) list) : bool = raise (Invalid_argument "Not implemented");;

let satisfiable (input : string list) : (string * bool) list list = raise (Invalid_argument "Not implemented");;