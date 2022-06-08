open Proj2_types;;

let buildParseTree (input : string list) : tree = 

    let rec parse_S (input: string list) =
        match input with
            | "(" :: t -> let (tree, st) = parse_T t in 
                                           (TreeNode("S", [TreeNode("(",[]) ; tree ; TreeNode(")",[])]), (List.tl st))

            | "and"::t | "or"::t | "not"::t -> let (tree, st) = parse_T input in 
                                                                (TreeNode("S", [TreeNode("(",[]) ; tree ; TreeNode(")",[])]), st)

            | str::t -> (TreeNode("S", [TreeNode(str, [])]), t)
            | _ -> raise(Invalid_argument "The Language doesn't support this")
  
    and parse_T (input: string list) =
        match input with
            | "not"::t -> let (tree, st) = parse_S t in (TreeNode("T", [TreeNode("not",[]) ; tree ]), st)

            | "and"::t -> let (tree1, st1) = parse_S t in
                          let (tree2, st2) = parse_S st1 in
                          (TreeNode("T", [TreeNode("and",[]) ; tree1 ;  tree2]), st2)

            | "or":: t -> let (tree1, st1) = parse_S t in
                          let (tree2, st2) = parse_S st1 in
                          (TreeNode("T", [TreeNode("or",[]) ; tree1 ; tree2]), st2)
    in
  
    let (tree, ls) = parse_S(input) in
    tree;;

let buildAbstractSyntaxTree (input : tree) : tree = 

        let rec shrink inp =
            match inp with
                TreeNode(str, rest) ->
                    (match str with
                        | "S" -> (match rest with
                                    | (hd::tl::tl2::_) -> shrink tl
                                    | (hd::_) -> match hd with
                                                | TreeNode(st,tr) -> TreeNode(st,[]))
                        | "T" -> (match rest with
                                    | (hd::t1::t2::_) -> (match hd with
                                                            | TreeNode("or",[]) -> TreeNode("or", [shrink t1 ; shrink t2])
                                                            | TreeNode("and",[]) -> TreeNode("and",[shrink t1 ; shrink t2]))
                                    | (hd::t1::_) -> TreeNode("not", [shrink t1]))

                        | _ -> raise(Invalid_argument ("Not supported by this grammar")))
        in
        (shrink input) ;;


let scanVariable (input : string list) : string list = 

    let checkVarPres (temp : string) (inputList : string list): bool =
        match temp with
            | "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" -> (not(List.mem temp inputList))
            | _ -> false
    in
    
    let rec traverse (input : string list) (output : string list) =
        match input with
            | [] -> output
            | (h::t) -> if (checkVarPres h output) then traverse t (h::output)
                        else traverse t output
    in
    (traverse input []) ;;

let generateInitialAssignList (varList : string list) : (string * bool) list = 

    let rec traverse (input : string list) (output : (string * bool) list) =
        match input with
            | [] -> output
            | (h::t) -> traverse t ((h,false)::output)
     in
traverse (List.rev varList) [] ;;

let generateNextAssignList (assignList : (string * bool) list) : (string * bool) list * bool = 

    let rec check (input : (string * bool) list) =
        match input with
            | [] -> true
            | (var,bol)::t -> if(bol) then false
                              else check t
    in

    let rec traverse (input : (string * bool) list) (output : (string * bool) list) (carry : bool) =
        match input with
            | [] -> output
            | (var,true)::t -> if (carry) then traverse t ((var,false)::output) true
                               else traverse t ((var,true)::output) false
            | (var,false)::t -> if (carry) then traverse t ((var,true)::output) false
                                else traverse t ((var,false)::output) false
        in
    
let finalList = traverse (List.rev assignList) [] true in
let finalCheck = check finalList in
(finalList, finalCheck);;

let lookupVar (assignList : (string * bool) list) (str : string) : bool = 
    
    let rec traverse (input : (string * bool) list) (inputString : string) =
        match input with
            | [] -> false
            | (var,bol)::t -> if(var = inputString) then bol
                              else traverse t str
        in

traverse assignList str ;;

let evaluateTree (t : tree) (assignList : (string * bool) list) : bool = 

    let rec traverse (t : tree) (assignList : (string * bool) list) : bool =
        match t with
            | TreeNode("TRUE", []) -> true
            | TreeNode("FALSE", []) -> false
            | TreeNode(str,[]) -> lookupVar assignList str
            | TreeNode("or", lt::rt::_) -> (traverse lt assignList) || (traverse rt assignList)
            | TreeNode("and", lt::rt::_) -> (traverse lt assignList) && (traverse rt assignList)
            | TreeNode("not", lt::_) -> not (traverse lt assignList)
            | TreeNode(_,_) -> raise(Invalid_argument "evalTree error not implemented")
    in
    
traverse t assignList ;;
 

let satisfiable (input : string list) : (string * bool) list list = 
    
    let vars = scanVariable(input) in
    let initialList = generateInitialAssignList vars in
    let parseTree = buildParseTree input in
    let asTree = buildAbstractSyntaxTree parseTree in

    let rec findcomb (input: tree) (asslist: (string * bool) list * bool) (output: (string * bool) list list) =
        match asslist with
            | (justlist,false) -> if((evaluateTree input justlist)) then findcomb input (generateNextAssignList justlist) (justlist::output)
                                  else findcomb input (generateNextAssignList justlist) output
            | (justlist,true) -> output
            | ([],_) -> output
    in
    
findcomb asTree (initialList, false) [] ;;