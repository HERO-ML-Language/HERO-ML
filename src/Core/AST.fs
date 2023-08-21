module AST

open Source_Ref
open Error

type Type =
    | Int
    | Float
    | Bool
    // num_dims = 0 represents "any number of dimensions", and is used for "empty"
    // and "all". It is also used during type analysis for bounds where the
    // number of dimensions could not be determined because of some error.
    | Bound of num_dims : int
    | Array of elem_type : Type * num_dims : int
    // The Unknown type is used during parsing as a placeholder for expressions
    // whose types cannot be determined until the type analysis step. It is also
    // used during type analysis for expressions containing errors.
    | Unknown

    member this.Str =
        let index_type_str num_dims =
            match num_dims with
            | 0 -> ["?"]
            | 1 -> ["int"]
            | _ -> "(int" :: (List.replicate (num_dims-1) ",int") @ [")"]
        match this with
        | Unknown -> "?"
        | Int     -> "int"
        | Float   -> "float"
        | Bool    -> "bool"
        | Bound num_dims ->
            String.concat "" ("Bound " :: (index_type_str num_dims))
        | Array (elem_type,num_dims) ->
            String.concat "" ("Array " :: (index_type_str num_dims) @ [" "; elem_type.Str])

    override this.ToString () = this.Str

// note that only non-negative values are used for valid variable IDs, whereas negative values are
// used, e.g., as placeholders for variables that haven't yet been mapped to their declarations
type Var_ID = int

type Node (src : Source_Ref, error : Error option) =
    member this.Src = src
    member this.Is_OK = error.IsNone
    member this.Is_Wrong = error.IsSome
    member this.Error = error.Value

    override this.ToString () = this.Src.Text

type Decl (name : string, id : Var_ID, type_ : Type, src : Source_Ref, ?error : Error) =
    inherit Node (src, error)
    member this.Name = name
    member this.Id = id
    member this.Type = type_

    new (error : Error, src : Source_Ref) = Decl ("", -1, Unknown, src, error)

type Index_Var (names : string list, ids : Var_ID list, comp_srcs : Source_Ref list, src : Source_Ref, ?error : Error) =
    inherit Node (src, error)
    member this.Comps = List.map3 (fun name id comp_src -> Decl (name, id, Int, comp_src)) names ids comp_srcs
    member this.Num_Dims = this.Comps.Length
    member this.Src = src

    // constructor to create a "wrong" node
    new (error : Error, src : Source_Ref) = Index_Var ([], [], [], src, error)

type Func =
    // misc. basic functions
    | If     of type_ : Type
    | Is_Def of type_ : Type
    | Cast_F_I | Cast_I_F

    // unary numeric functions
    | Neg_I | Neg_F
    | Exp | Sqrt

    // infix numeric operators
    | Add_I | Sub_I | Mul_I | Div_I | Mod
    | Add_F | Sub_F | Mul_F | Div_F
    | L_Shift | R_Shift
    | LT_I | LE_I | GE_I | GT_I
    | LT_F | LE_F | GE_F | GT_F
    | Eq_I | NE_I
    | Eq_F | NE_F
    | Eq_B | NE_B

    // boolean operators
    | Not | And | Or

    // functions on bounds
    | Size         of num_dims : int
    | Is_Finite    of num_dims : int
    | Is_Dense     of num_dims : int
    | Is_Sparse    of num_dims : int
    | Is_Predicate of num_dims : int
    | Is_Product   of num_dims : int
    | Join         of num_dims : int
    | Meet         of num_dims : int
    | Bound_Prod   of num_dims : int

    // array functions
    | Bound       of elem_type : Type * num_dims : int
    | Slice_Array of elem_type : Type * num_dims : int

    member this.Str_ add_parens =
        let par_func str =
            if add_parens then str + "()"
            else str
        match this with
        // infix operators
        | Neg_I | Neg_F      -> "-"
        | Add_I | Add_F      -> "+"
        | Sub_I | Sub_F      -> "-"
        | Mul_I | Mul_F      -> "*"
        | Div_I | Div_F      -> "/"
        | Mod                -> "%"
        | L_Shift            -> "<<"
        | R_Shift            -> ">>"
        | LT_I | LT_F        -> "<"
        | LE_I | LE_F        -> "<="
        | GE_I | GE_F        -> ">="
        | GT_I | GT_F        -> ">"
        | Eq_I | Eq_F | Eq_B -> "="
        | NE_I | NE_F | NE_B -> "!="
        | And                -> "&&"
        | Or                 -> "||"
        | Bound_Prod  _      -> "()"
        | Slice_Array _      -> "|"
        // named functions
        | If           _ -> "if"          |> par_func
        | Is_Def       _ -> "isDef"       |> par_func
        | Cast_F_I       -> "int"         |> par_func
        | Cast_I_F       -> "float"       |> par_func
        | Exp            -> "exp"         |> par_func
        | Sqrt           -> "sqrt"        |> par_func
        | Not            -> "not"         |> par_func
        | Size         _ -> "size"        |> par_func
        | Is_Finite    _ -> "finite"      |> par_func
        | Is_Dense     _ -> "isDense"     |> par_func
        | Is_Sparse    _ -> "isSparse"    |> par_func
        | Is_Predicate _ -> "isPredicate" |> par_func
        | Is_Product   _ -> "isProduct"   |> par_func
        | Join         _ -> "join"        |> par_func
        | Meet         _ -> "meet"        |> par_func
        | Bound        _ -> "bound"       |> par_func

    member this.Str = this.Str_ false
    member this.Str_P = this.Str_ true
    override this.ToString () = this.Str_P

// higher order functions
type HO_Func =
    | Reduce of elem_type : Type * num_dims : int
    | Scan   of elem_type : Type * num_dims : int

    member this.Str_ add_parens =
        let str =
            match this with
            | Reduce _ -> "reduce"
            | Scan _   -> "scan"
        if add_parens then str + "()" else str

    member this.Str = this.Str_ false
    member this.Str_P = this.Str_ true
    override this.ToString () = this.Str_P

type Expr (expr' : Expr', src : Source_Ref, ?error : Error) =
    inherit Node (src, error)
    member this.Expr' = expr'

    // constructor to create a "wrong" node
    new (error : Error, src : Source_Ref) = Expr (Int_Const 0, src, error)

    member this.Type =
        if this.Is_Wrong then
            Unknown
        else
            match this.Expr' with
            | Undef_Const type_ -> type_
            | Error_Const type_ -> type_
            | Int_Const _   -> Int
            | Float_Const _ -> Float
            | Bool_Const _  -> Bool
            | Bound_Const _ -> Type.Bound 0
            | Var (_,_,type_) -> type_
            | In type_ -> type_
            | Array_Access (array,_) ->
                match array.Type with
                | Array (elem_type,_) -> elem_type
                | _ -> Unknown
            // bounds
            | Dense_Bound _ -> Type.Bound 1
            | Sparse_Bound elems -> Type.Bound elems.Head.Num_Dims
            | Pred_Bound (var,_) -> Type.Bound var.Num_Dims
            // arrays
            | Dense_Array (bound,elems) -> Array (elems.Head.Type, bound.Length)
            | Sparse_Array (indices,elems) -> Array (elems.Head.Type, indices.Head.Num_Dims)
            | Array_Compr (var,elem_expr,_) -> Array (elem_expr.Type, var.Num_Dims)
            | Forall (var,elem_expr) -> Array (elem_expr.Type, var.Num_Dims)
            // function applications
            | Func_Appl (If type_, _) -> type_
            | Func_Appl ((Cast_F_I | Neg_I | Add_I | Sub_I | Mul_I | Div_I | Mod | L_Shift | R_Shift | Size _), _) -> Int
            | Func_Appl ((Cast_I_F | Neg_F | Exp | Sqrt | Add_F | Sub_F | Mul_F | Div_F), _) -> Float
            | Func_Appl ((Is_Def _
                        | LT_I | LT_F | LE_I | LE_F | GE_I | GE_F | GT_I | GT_F
                        | Eq_I | Eq_F | Eq_B | NE_I | NE_F | NE_B
                        | Not | And | Or
                        | Is_Finite _ | Is_Dense _ | Is_Sparse _ | Is_Predicate _ | Is_Product _), _) -> Bool
            | Func_Appl ((Join num_dims | Meet num_dims), _) -> Type.Bound num_dims
            | Func_Appl (Bound_Prod num_dims, _) -> Type.Bound num_dims
            | Func_Appl (Bound (_, num_dims), _) -> Type.Bound num_dims
            | Func_Appl (Slice_Array (elem_type, num_dims), _) -> Array (elem_type, num_dims)
            | Member_Func_Appl _ -> Bool
            | HO_Func_Appl (Reduce (elem_type, _), _, _) -> elem_type
            | HO_Func_Appl (Scan (elem_type, num_dims), _, _) -> Array (elem_type, num_dims)

and Expr' =
    | Undef_Const of type_ : Type
    | Error_Const of type_ : Type
    | Int_Const   of int
    | Float_Const of float
    | Bool_Const  of bool
    | Bound_Const of is_all : bool // true = all, false = empty
    // note: `id' is unique among variables (declarations) in a program, whereas the name can be
    // shared if a local variable "captures" the name of a variable defined in an outer scope
    | Var of name : string * id : Var_ID * type_ : Type
    | In of type_ : Type
    | Array_Access of array : Expr * index : Index_Expr
    // bounds --------------------------------------------------
    | Dense_Bound of l : Expr * u : Expr
    | Sparse_Bound of elems : Index_Expr list
    | Pred_Bound of var : Index_Var * pred : Expr
    // arrays --------------------------------------------------
    // `bound' represents a product of dense bounds, where each bound is represented by one or two
    // expressions giving the endpoints of the bound, as well as a constant delta giving the second
    // endpoint relative to the first. The delta is used even if an expression for the second
    // endpoint is given explicitly, because the latter needs to be evaluated and checked during
    // runtime for equality with the first endpoint plus the delta. The delta is negative if the
    // first expression specifies the upper endpoint of the interval (and the interval spans more
    // than one value), otherwise it's non-negative.
    | Dense_Array of bound : (Expr * Expr option * int) list * elems : Expr list
    | Sparse_Array of indices : Index_Expr list * elems : Expr list
    | Array_Compr of var : Index_Var * elem_expr : Expr * bound : Expr
    | Forall of var : Index_Var * elem_expr : Expr
    // function applications --------------------------------------------------
    | Func_Appl of func : Func * args : Expr list
    // member() gets its own AST node type since it is the only function taking
    // an index as an argument
    | Member_Func_Appl of num_dims : int * index_arg : Index_Expr * bound_arg : Expr
    | HO_Func_Appl of func : HO_Func * func_arg : Func * arg : Expr

and Index_Expr (comps : Expr list, src : Source_Ref, ?error : Error) =
    inherit Node (src, error)
    member this.Comps = comps
    member this.Num_Dims = comps.Length

    // constructor to create a "wrong" node
    new (error : Error, src : Source_Ref) = Index_Expr ([], src, error)

let get_child_exprs (expr : Expr) : Expr list =
    match expr.Expr' with
    | Undef_Const _ | Error_Const _ | Int_Const _ | Float_Const _ | Bool_Const _ | Bound_Const _ | Var _ | In _ -> []
    | Array_Access (array,index) -> array :: index.Comps
    | Dense_Bound (l,u) -> [l;u]
    | Sparse_Bound elems -> elems |> List.collect (fun idx -> idx.Comps)
    | Pred_Bound (_,pred) -> [pred]
    | Dense_Array (bound,elems) -> (bound |> List.collect (fun (a,b,_) -> a :: Option.toList b)) @ elems
    | Sparse_Array (indices,elems) -> (indices |> List.collect (fun idx -> idx.Comps)) @ elems
    | Array_Compr (_,elem_expr,bound) -> [elem_expr;bound]
    | Forall (_,elem_expr) -> [elem_expr]
    | Func_Appl (_,args) -> args
    | Member_Func_Appl (_,index_arg,bound_arg) -> bound_arg :: index_arg.Comps
    | HO_Func_Appl (_,_,arg) -> [arg]

type Stmt (stmt' : Stmt', src : Source_Ref, ?error : Error) =
    inherit Node (src, error)
    member this.Stmt' = stmt'

    // constructor to create a "wrong" node
    new (error : Error, src : Source_Ref) = Stmt (Skip, src, error)

and Stmt' =
    | Skip
    | Assign of lhs_name : string * lhs_id : Var_ID * lhs_indices : Index_Expr list * rhs : Expr
    | If of cond : Expr * then_block : Stmt list * else_block : Stmt list
    | While of cond : Expr * body : Stmt list
    | Foreach of var : Index_Var * bound : Expr * lhs_name : string * lhs_id : Var_ID * lhs_indices : Index_Expr list * rhs : Expr
    | Out of exprs : Expr list

type Prog (decls : Decl list, stmts : Stmt list, src : Source_Ref, ?error : Error) =
    inherit Node (src, error)
    member this.Decls = decls
    member this.Stmts = stmts

    // constructor to create a "wrong" node
    new (error : Error, src : Source_Ref) = Prog ([], [], src, error)
