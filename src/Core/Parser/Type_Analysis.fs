module Type_Analysis

open Source_Ref
open Error
open AST

type Sym_Tab = Map<string, Decl>

type Error_Collector () =
    member this.Bind ((x, es : Error list), f) =
        let y, es' = f x
        y, es @ es'

    member this.Bind (es : Error list, f) = this.Bind (((),es), f)
    member this.Bind (e : Error, f) = this.Bind ([e],f)

    member this.Delay (f) = f ()
    member this.Combine (((),es1),(y,es2)) = y, es1 @ es2

    member this.Return (x) = x,[]
    member this.ReturnFrom ((x, es : Error list)) = x,es
    member this.ReturnFrom ((x, e : Error)) = this.ReturnFrom ((x,[e]))
    member this.Zero () = this.Return ()

let err_coll = new Error_Collector ()

let map f l = List.map f l |> List.unzip |> (fun (l',e) -> l', List.concat e)

let test_cond' (msg : string) (src : Source_Ref) (cond : bool) : Error list =
    if cond then [] else [Error (src,msg)]

let test_cond msg_fmt = Printf.kprintf test_cond' msg_fmt

// The following two functions define the rules for which types are considered compatible with each
// other. Conceptually, `types_match' tests whether it would be valid to assign a value of type
// `type2' to a variable declared with type `type1' (notwithstanding that the language might not
// actually allow declaring variables of this type). If type1 = type2 then obviously it would be.
// If type1 = Unknown and/or type2 = Unknown then something is wrong, but we trust that an error
// message has already been generated elsewhere in the type analysis so we "pretend" that the types
// are compatible and say nothing. If both types are bounds but with different numbers of
// dimensions, then this is OK if one of them has "0 dimensions". This represents "any number of
// dimensions", and is used for the special bounds "empty" and "all" (note that if a value of type
// Bound 0 were assigned to a variable of type Bound d for some d > 0, then the assigned value would
// be implicitly "cast" to also have type Bound d). During the type analysis, 0 dimensions is also
// used as a placeholder in bounds where something has gone wrong, analogous to how the Unknown type
// is used. If both types are arrays then, provided their dimensions match according to the same
// criteria as for bounds, their element types are checked recursively.
// (Note: both `dims_match' and `types_match' are commutative.)

let dims_match dims1 dims2 = dims1 = dims2 || dims1 = 0 || dims2 = 0

let rec types_match type1 type2 =
    match type1, type2 with
    | Unknown, _ | _, Unknown -> true
    | Type.Bound d1, Type.Bound d2 -> dims_match d1 d2
    | Array (elem_type1, d1), Array (elem_type2, d2) ->
        (dims_match d1 d2) && types_match elem_type1 elem_type2
    | _, _ -> type1 = type2

let test_type' msg_fmt =
    Printf.kprintf (fun (msg : string) (exp_type : Type) (src : Source_Ref) (expr : Expr) ->
        test_cond' msg src (types_match exp_type expr.Type)) msg_fmt

let test_type msg_fmt =
    Printf.kprintf (fun (msg : string) (exp_type : Type) (expr : Expr) ->
        test_cond' msg expr.Src (types_match exp_type expr.Type)) msg_fmt

let test_types msg_fmt =
    Printf.kprintf (fun (msg : string) (exp_types : Type list) (expr : Expr) ->
        let actual = expr.Type
        test_cond' msg expr.Src (exp_types |> List.exists (types_match actual))) msg_fmt

let test_type_bound msg_fmt =
    Printf.kprintf (fun (msg : string) (expr : Expr) ->
        match expr.Type with
        | Type.Bound num_dims -> num_dims, []
        | Unknown -> 0, []
        | _ -> 0, [Error (expr.Src,msg)]) msg_fmt

let test_type_array' msg_fmt =
    Printf.kprintf (fun (msg : string) (src : Source_Ref) (expr : Expr) ->
        match expr.Type with
        | Array (elem_type,num_dims) -> (elem_type,num_dims), []
        | Unknown -> (Unknown,0), []
        | _ -> (Unknown,0), [Error (src,msg)]) msg_fmt

let test_type_array msg_fmt =
    Printf.kprintf (fun (msg : string) (expr : Expr) ->
        test_type_array' "%s" msg expr.Src expr) msg_fmt

let test_same_dims msg_fmt =
    Printf.kprintf (fun (msg : string) (indices : Index_Expr list) ->
        let filtered = indices |> List.filter (fun index -> index.Is_OK)
        match filtered with
        | [] | [_] -> []
        | head::tail ->
            let common_dims = head.Num_Dims
            tail |> List.tryFind (fun index -> index.Num_Dims <> common_dims)
                |> Option.map (fun mismatch -> Error (mismatch.Src, msg))
                |> Option.toList) msg_fmt

let update_sym_tab_with_decls (sym_tab : Sym_Tab) (decls : Decl list) : Sym_Tab * Error list =
    // begin by generating a symbol table in which there should be no name collision (to check that
    // there are no collisions among the names in `decls')
    let error_dup = make_error "A variable named \"%s\" has already been declared at %s"
    let coll_free, errors =
        ((Sym_Tab [], []), decls)
        ||> List.fold (fun (st,errors) decl ->
            if decl.Is_Wrong then
                st, decl.Error::errors
            else
                match Map.tryFind decl.Name st with
                | None ->
                    Map.add decl.Name decl st, errors
                | Some prev ->
                    let e = error_dup decl.Name prev.Src.Str_S decl.Src
                    st, e::errors)
    // now (over-)write `coll_free' to `sym_tab' (new declarations shadow old ones in case of name conflicts)
    let upd = (sym_tab, Map.toSeq coll_free) ||> Seq.fold (fun st (name,decl) -> Map.add name decl st)
    upd, errors

let update_sym_tab_with_index_var (sym_tab : Sym_Tab) (index_var : Index_Var) : Sym_Tab * Error list =
    if index_var.Is_Wrong then
        sym_tab, [index_var.Error]
    else
        update_sym_tab_with_decls sym_tab index_var.Comps

let rec check_expr (sym_tab : Sym_Tab) (expr : Expr) : Expr * Error list =
    let check_expr' = check_expr sym_tab
    if expr.Is_Wrong then
        expr, [expr.Error]
    else
        let src = expr.Src
        let expr', errors =
            match expr.Expr' with
            | Undef_Const _ | Error_Const _ | Int_Const _ | Float_Const _
            | Bool_Const _ | Bound_Const _ | In _ -> err_coll { return expr.Expr' }
            | Var (name,_,_) -> err_coll {
                match Map.tryFind name sym_tab with
                | Some decl -> return Var (name, decl.Id, decl.Type)
                | None -> return! expr.Expr', make_error "Undefined identifier \"%s\"" name src
                }
            | Array_Access (array,index) -> err_coll {
                let! array = check_expr' array
                let! index = check_index_expr sym_tab index
                let! _, arr_dims = test_type_array' "Only arrays can be indexed" index.Src array
                do! test_cond
                      "%d-dimensional index cannot be used to access %d-dimensional array"
                      index.Num_Dims arr_dims index.Src
                      (dims_match index.Num_Dims arr_dims)
                return Array_Access (array,index)
                }
            | Dense_Bound (l,u) -> err_coll {
                let! l = check_expr' l
                let! u = check_expr' u
                do! List.collect (test_type "Index range endpoints must have type int" Int) [l;u]
                return Dense_Bound (l,u)
                }
            | Sparse_Bound elems -> err_coll {
                let! elems = elems |> map (check_index_expr sym_tab)
                do! test_same_dims "Elements of explicit bound must be integers or integer tuples with the same number of dimensions" elems
                return Sparse_Bound elems
                }
            | Pred_Bound (var,pred) -> err_coll {
                let! tmp_sym_tab = update_sym_tab_with_index_var sym_tab var
                let! pred = check_expr tmp_sym_tab pred
                do! test_type "Predicate must have type bool" Bool pred
                return Pred_Bound (var,pred)
                }
            | Dense_Array (bound,elems) -> err_coll {
                let test_int = test_type "Index range endpoints must have type int" Int
                let! bound = bound |> map (fun (a,b,d) -> err_coll {
                    let! a = check_expr' a
                    do! test_int a
                    if b.IsNone then
                        return (a,b,d)
                    else
                        let! b' = check_expr' b.Value
                        do! test_int b'
                        return (a,Some b',d)
                    })
                let! elems = check_arr_elems sym_tab elems
                return Dense_Array (bound,elems)
                }
            | Sparse_Array (indices,elems) -> err_coll {
                let! indices = indices |> map (check_index_expr sym_tab)
                do! test_same_dims "Indices in explicit array expression must be integers or integer tuples with the same number of dimensions" indices
                let! elems = check_arr_elems sym_tab elems
                return Sparse_Array (indices,elems)
                }
            | Array_Compr (var,elem_expr,bound) -> err_coll {
                let! tmp_sym_tab = update_sym_tab_with_index_var sym_tab var
                let! elem_expr = check_expr tmp_sym_tab elem_expr
                let! bound = check_expr' bound
                let! bnd_dims = test_type_bound "Expression after \"in\" must be of type bound" bound
                do! test_cond
                      "The given element has %d dimensions, but the bound at %s has %d dimensions"
                      var.Num_Dims bound.Src.Str_S bnd_dims var.Src
                      (dims_match var.Num_Dims bnd_dims)
                return Array_Compr (var,elem_expr,bound)
                }
            | Forall (var,elem_expr) -> err_coll {
                let! tmp_sym_tab = update_sym_tab_with_index_var sym_tab var
                let! elem_expr = check_expr tmp_sym_tab elem_expr
                return Forall (var,elem_expr)
                }
            | Func_Appl (func,args) -> err_coll {
                // checks that `args' has the correct length, recursively type checks all the
                // arguments (even any excess ones if there are too many), and finally truncates
                // `args' to the right length if necessary
                let check_args (exp_num_args : int) : Expr list * Error list = err_coll {
                    let error =
                        match exp_num_args with
                        | 1 -> make_error "%s expects a single argument" func.Str_P
                        | 2 -> make_error "%s expects two arguments" func.Str_P
                        | 3 -> make_error "%s expects three arguments" func.Str_P
                        | _ -> make_error "%s expects %d arguments" func.Str_P exp_num_args
                    let num_args = args.Length
                    if num_args < exp_num_args then
                        do! error (Source_Ref.merge args.Head.Src (List.last args).Src)
                    elif num_args > exp_num_args then
                        do! error (Source_Ref.merge args[exp_num_args].Src (List.last args).Src)
                    let! args = map check_expr' args
                    return List.truncate exp_num_args args
                }
                // if one of the arguments is a float and the other an int, tries to reinterpret the
                // int as a float (`arg1' and `arg2' are assumed to have already been checked once,
                // so any errors found during the second check are ignored)
                let recheck_args (arg1 : Expr) (arg2 : Expr) : Expr * Expr =
                    let t1, t2 = arg1.Type, arg2.Type
                    let arg1 = if t1 = Int && t2 = Float then recheck_expr_as_float sym_tab arg1 |> fst else arg1
                    let arg2 = if t1 = Float && t2 = Int then recheck_expr_as_float sym_tab arg2 |> fst else arg2
                    arg1, arg2
                match func with
                | Func.If _ ->
                    let test_bool = test_type "First argument to %s must have type bool" func.Str_P Bool
                    let! args = check_args 3
                    match args with
                    | cond::arg2::arg3::_ ->
                        do! test_bool cond
                        let arg2, arg3 = recheck_args arg2 arg3
                        let t2, t3 = arg2.Type, arg3.Type
                        do! test_cond
                              "Second and third argument to %s must have the same type" func.Str_P
                              (Source_Ref.merge arg2.Src arg3.Src)
                              (types_match t2 t3)
                        let type_ = if t2 = t3 then t2 else Unknown
                        return Func_Appl (Func.If type_, [cond;arg2;arg3])
                    | [cond;arg2] ->
                        do! test_bool cond
                        return Func_Appl (Func.If arg2.Type, args)
                    | [cond] ->
                        do! test_bool cond
                        return Func_Appl (Func.If Unknown, args)
                    | [] ->
                        return Func_Appl (Func.If Unknown, args)
                | Is_Def _ ->
                    let! args = check_args 1
                    match args with
                    | arg::_ -> return Func_Appl (Is_Def arg.Type, args)
                    | [] -> return Func_Appl (Is_Def Unknown, args)
                | Cast_F_I | Exp | Sqrt ->
                    let! args = check_args 1
                    match args with
                    | arg::_ ->
                        let arg = recheck_expr_as_float sym_tab arg |> fst
                        do! test_type "Argument to %s must have type float" func.Str_P Float arg
                        return Func_Appl (func,[arg])
                    | [] ->
                        return Func_Appl (func,args)
                | Cast_I_F | Not ->
                    let! args = check_args 1
                    match args with
                    | arg::_ ->
                        let type_ = match func with Cast_I_F -> Int | Not | _ -> Bool
                        do! test_type "Argument to %s must have type %s" func.Str_P type_.Str type_ arg
                    | [] -> ()
                    return Func_Appl (func,args)
                | Neg_I ->
                    let! args = check_args 1
                    match args with
                    | arg::_ ->
                        let! func =
                            match arg.Type with
                            | Int | Unknown -> Neg_I, []
                            | Float -> Neg_F, []
                            | _ -> Neg_I, [Error (arg.Src, "Only scalar numerical expressions can be negated")]
                        return Func_Appl (func,args)
                    | [] ->
                        return Func_Appl (func,args)
                | Add_I | Sub_I | Mul_I | Div_I
                | LT_I | LE_I | GE_I | GT_I ->
                    let! type_, args = err_coll {
                        let! args = check_args 2
                        match args with
                        | arg1::arg2::_ ->
                            let arg1, arg2 = recheck_args arg1 arg2
                            let t1, t2 = arg1.Type, arg2.Type
                            let errors = List.collect (
                                test_types
                                    "Operands to %s must have type int or float"
                                    func.Str_P [Int;Float]) [arg1;arg2]
                            // only if both arguments have valid types do we bother to check that the
                            // types are equal
                            if errors.IsEmpty then
                                let src = Source_Ref.merge arg1.Src arg2.Src
                                do! test_cond
                                      "Operands to %s must have the same type (int or float)"
                                      func.Str_P src
                                      (types_match t1 t2)
                            else
                                do! errors
                            let type_ =
                                // if the operands have the wrong types we make a best guess at the
                                // intended type of the expression
                                match t1,t2 with
                                | (Float,_) | (_,Float) -> Float
                                | (Int,_) | (_,Int) -> Int
                                | _ -> Unknown
                            return type_, [arg1;arg2]
                        | [arg1] -> return arg1.Type, args
                        | [] -> return Unknown, args
                        }
                    let func =
                        match func, type_ with
                        | Neg_I, Float -> Neg_F
                        | Add_I, Float -> Add_F
                        | Sub_I, Float -> Sub_F
                        | Mul_I, Float -> Mul_F
                        | Div_I, Float -> Div_F
                        | LT_I, Float -> LT_F
                        | LE_I, Float -> LE_F
                        | GE_I, Float -> GE_F
                        | GT_I, Float -> GT_F
                        | _ -> func
                    return Func_Appl (func,args)
                | L_Shift | R_Shift ->
                    let! args = check_args 2
                    do! args |> List.collect (test_type "Operands to %s must have type int" func.Str_P Int)
                    return Func_Appl (func,args)
                | Eq_I | NE_I ->
                    let! type_, args = err_coll {
                        let! args = check_args 2
                        match args with
                        | arg1::arg2::_ ->
                            let arg1, arg2 = recheck_args arg1 arg2
                            let t1, t2 = arg1.Type, arg2.Type
                            let errors = List.collect (
                                test_types
                                    "Operands to %s must have type int, float, or bool"
                                    func.Str_P [Int;Float;Bool]) [arg1;arg2]
                            // only if both arguments have valid types do we bother to check that the
                            // types are equal
                            if errors.IsEmpty then
                                let src = Source_Ref.merge arg1.Src arg2.Src
                                do! test_cond
                                      "Operands to %s must have the same type (int, float, or bool)"
                                      func.Str_P src
                                      (types_match t1 t2)
                            else
                                do! errors
                            // if the operands have the wrong types we make a best guess at the
                            // intended type of the expression
                            let type_ =
                                match t1,t2 with
                                | (Float,_) | (_,Float) -> Float
                                | (Int,_) | (_,Int) -> Int
                                | (Bool,_) | (_,Bool) -> Bool
                                | _ -> Unknown
                            return type_, [arg1;arg2]
                        | [arg1] -> return arg1.Type, args
                        | [] -> return Unknown, args
                        }
                    let func =
                        match func, type_ with
                        | Eq_I, Float -> Eq_F
                        | NE_I, Float -> NE_F
                        | Eq_I, Bool -> Eq_B
                        | NE_I, Bool -> NE_B
                        | _ -> func
                    return Func_Appl (func,args)
                | Neg_F | Add_F | Sub_F | Mul_F | Div_F
                | LT_F | LE_F | GE_F | GT_F
                | Eq_F | NE_F
                | Eq_B | NE_B ->
                    failwith "The parser shouldn't generate these"
                    return Func_Appl (func,args) // to silence compiler error
                | Mod ->
                    let! args = check_args 2
                    do! args |> List.collect (test_type "Operands to %s must have type int" func.Str_P Int)
                    return Func_Appl (func,args)
                | And | Or ->
                    let! args = check_args 2
                    do! args |> List.collect (test_type "Operands to %s must have type bool" func.Str_P Bool)
                    return Func_Appl (func,args)
                | Size _ | Is_Finite _ | Is_Dense _ | Is_Sparse _ | Is_Predicate _ | Is_Product _ ->
                    let! args = check_args 1
                    let! num_dims =
                        match args with
                        | arg::_ -> test_type_bound "Argument to %s must be of type bound" func.Str_P arg
                        | [] -> 0, []
                    let func = (
                        match func with
                        | Size _ -> Size
                        | Is_Finite _ -> Is_Finite
                        | Is_Dense _ -> Is_Dense
                        | Is_Sparse _ -> Is_Sparse
                        | Is_Predicate _ -> Is_Predicate
                        | Is_Product _ | _ -> Is_Product) num_dims
                    return Func_Appl (func,args)
                | Join _ | Meet _ ->
                    let! args = check_args 2
                    let! num_dims =
                        let test_bnd = test_type_bound "Arguments to %s must be of type bound" func.Str_P
                        match args with
                        | arg1::arg2::_ -> err_coll {
                            let! dims1 = test_bnd arg1
                            let! dims2 = test_bnd arg2
                            match dims1, dims2 with
                            | 0,d | d,0 -> return d
                            | _ ->
                                do! test_cond
                                      "The bound at %s has %d dimensions, but the bound at %s has %d dimensions"
                                      arg1.Src.Str_S dims1 arg2.Src.Str_S dims2 arg2.Src
                                      (dims1 = dims2)
                                return dims1
                            }
                        | [arg1] -> test_bnd arg1
                        | [] -> 0, []
                    let func = match func with Join _ -> Join num_dims | _ -> Meet num_dims
                    return Func_Appl (func,args)
                | Bound_Prod _ ->
                    do! test_cond "Bound products must have at least two factors" src (args.Length >= 2)
                    let! args = map check_expr' args
                    // calculate the number of dimensions
                    let! num_dims =
                        let error_dims =
                            make_error
                                "Only one-dimensional factors are allowed in bound products. \
                                 This factor has %d dimensions"
                        let error_fac = make_error "Only bounds are allowed as factors in bound products"
                        ((0,[]), args)
                        ||> List.fold (fun (d,es) a ->
                            match a.Type with
                            | Type.Bound num_dims when num_dims < 2 ->
                                // `num_dims' can be 0 for "empty" and "all", but they become
                                // one-dimensional when used as factors
                                d+1, es
                            // everything else is an error
                            | Type.Bound num_dims ->
                                // we add num_dims to sum anyway as a best guess as to the intended number of dimensions
                                d+num_dims, (error_dims num_dims a.Src)::es
                            | _ ->
                                d+1, (error_fac a.Src)::es)
                    return Func_Appl (Bound_Prod num_dims, args)
                | Func.Bound _ ->
                    let! args = check_args 1
                    match args with
                    | arg::_ ->
                        let! elem_type, num_dims =
                            test_type_array "Argument to %s must be of array type" func.Str_P arg
                        return Func_Appl (Func.Bound (elem_type,num_dims), args)
                    | [] -> return Func_Appl (Func.Bound (Unknown,0), args)
                | Slice_Array _ ->
                    let! args = check_args 2
                    match args with
                    | arg1::arg2::_ ->
                        let! elem_type, arr_dims =
                            test_type_array' "Cannot take sub-array of an expression of type %s" arg1.Type.Str src arg1
                        let! bnd_dims = test_type_bound "Second operand to %s must be of type bound" func.Str_P arg2
                        do! test_cond
                              "%d-dimensional bound cannot be used to take sub-array of %d-dimensional array"
                              bnd_dims arr_dims arg2.Src
                              (dims_match arr_dims bnd_dims)
                        return Func_Appl (Slice_Array (elem_type, arr_dims), args)
                    | [arg1] ->
                        let! elem_type, num_dims =
                            test_type_array "First operand to %s must be of array type" func.Str_P arg1
                        return Func_Appl (Slice_Array (elem_type, num_dims), args)
                    | [] ->
                        return Func_Appl (Slice_Array (Unknown,0), args)
                }
            | Member_Func_Appl (_,index_arg,bound_arg) -> err_coll {
                let! index_arg = check_index_expr sym_tab index_arg
                let! bound_arg = check_expr' bound_arg
                let! bnd_dims = test_type_bound "Second argument to member() must be of type bound" bound_arg
                do! test_cond
                      "The given element has %d dimensions, but the bound at %s has %d dimensions"
                      index_arg.Num_Dims bound_arg.Src.Str_S bnd_dims index_arg.Src
                      (dims_match index_arg.Num_Dims bnd_dims)
                return Member_Func_Appl (bnd_dims,index_arg,bound_arg)
                }
            | HO_Func_Appl (func,func_arg,arr_arg) -> err_coll {
                let! arr_arg = check_expr' arr_arg
                let! elem_type, num_dims = test_type_array "Second argument to %s must be of array type" func.Str_P arr_arg
                let func = (match func with Reduce _ -> Reduce | Scan _ -> Scan) (elem_type, num_dims)
                let! func_arg =
                    match func_arg, elem_type with
                    | Add_I, (Int | Unknown) -> Add_I, []
                    | Sub_I, (Int | Unknown) -> Sub_I, []
                    | Mul_I, (Int | Unknown) -> Mul_I, []
                    | Div_I, (Int | Unknown) -> Div_I, []
                    | Add_I, Float -> Add_F, []
                    | Sub_I, Float -> Sub_F, []
                    | Mul_I, Float -> Mul_F, []
                    | Div_I, Float -> Div_F, []
                    | (Add_I | Sub_I | Mul_I | Div_I), _ ->
                        func_arg,
                        [make_error
                            "With %s as the first argument to %s, the second argument must be a numeric array"
                            func_arg.Str func.Str_P arr_arg.Src]
                    | (And | Or), (Bool | Unknown) -> func_arg, []
                    | (And | Or), _ ->
                        func_arg,
                        [make_error
                            "With %s as the first argument to %s, the second argument must be a boolean array"
                            func_arg.Str func.Str_P arr_arg.Src]
                    | Join _, Type.Bound num_dims -> Join num_dims, []
                    | Meet _, Type.Bound num_dims -> Meet num_dims, []
                    | Join _, Unknown -> Join 0, []
                    | Meet _, Unknown -> Meet 0, []
                    | (Join _| Meet _), _ ->
                        func_arg,
                        [make_error
                            "With %s as the first argument to %s, the second argument must be an array of bounds"
                            func_arg.Str func.Str_P arr_arg.Src]
                    | _ ->
                        func_arg,
                        [make_error "Operator %s is not supported by %s" func_arg.Str func.Str_P src]
                return HO_Func_Appl (func,func_arg,arr_arg)
                }
        Expr (expr',src), errors

and recheck_expr_as_float (sym_tab : Sym_Tab) (expr : Expr) : Expr * Error list = err_coll {
    let src = expr.Src
    match expr.Expr' with
    | Int_Const c ->
        return Expr (Float_Const (float c), src)
    | Func_Appl (Neg_I, [arg]) ->
        let! arg = recheck_expr_as_float sym_tab arg
        let func = if arg.Type = Float then Neg_F else Neg_I
        return Expr (Func_Appl (func,[arg]), src)
    | _ ->
        return expr
}

and check_arr_elems (sym_tab : Sym_Tab) (elems : Expr list) : Expr list * Error list = err_coll {
    // recursively check elements
    let! elems =
        let zipped = List.map (check_expr sym_tab) elems
        let unzip = List.unzip >> (fun (elems,errors) -> elems, List.concat errors)
        // if at least one element has type float, any bare integer literals should be implicitly
        // recast as floats
        let has_float = zipped |> List.exists (fun (elem,_) -> elem.Type = Float)
        if has_float then
            zipped
            |> List.map (fun (elem,el_errors) ->
                if elem.Type = Int then
                    recheck_expr_as_float sym_tab elem
                else
                    (elem,el_errors))
            |> unzip
        else
            unzip zipped
    // check that all elements whose types are not Unknown have the same type as the first such
    // element. Otherwise generate an error on the first offending element.
    let fst_type = elems |> List.tryPick (fun elem ->
        if elem.Type <> Unknown then Some elem.Type else None)
    match fst_type with
    | None ->
        // all elements have type Unknown
        return elems
    | Some fst_type ->
        let fst_mismatch = elems |> List.tryFind (fun elem -> elem.Type <> Unknown && elem.Type <> fst_type)
        match fst_mismatch with
        | None -> ()
        | Some fst_mismatch ->
            do! make_error
                  "All elements of an explicit array must have the same type. \
                   This element has type %s but was expected to have type %s"
                  fst_mismatch.Type.Str fst_type.Str fst_mismatch.Src 
        return elems
}

and check_index_expr (sym_tab : Sym_Tab) (expr : Index_Expr) : Index_Expr * Error list = err_coll {
    if expr.Is_Wrong then
        return! expr, expr.Error
    else
        let! comps = map (check_expr sym_tab) expr.Comps
        do! comps |> List.collect (test_type "Only integers and integer tuples can be used as indices" Int)
        return Index_Expr (comps,expr.Src)
}

let rec check_stmt (sym_tab : Sym_Tab) (stmt : Stmt) : Stmt * Error list =
    let check_stmts = map (check_stmt sym_tab)
    let check_arr_access (sym_tab : Sym_Tab) (var_name : string) (indices : Index_Expr list) : (Var_ID * Index_Expr list * Type) * Error list =
        err_coll {
            let! indices = indices |> map (check_index_expr sym_tab)
            match Map.tryFind var_name sym_tab with
            | Some decl ->
                let! elem_type =
                    ((decl.Type, []), indices)
                    ||> List.fold (fun (arr_type,errors) idx ->
                        match arr_type with
                        | Array (elem_type,arr_dims) ->
                            elem_type,
                            (test_cond
                                "%d-dimensional index cannot be used to access %d-dimensional array"
                                idx.Num_Dims arr_dims idx.Src
                                (dims_match idx.Num_Dims arr_dims)) @ errors
                        | Unknown ->
                            Unknown, errors
                        | _ ->
                            Unknown, Error (idx.Src, "Only arrays can be indexed")::errors)
                return decl.Id, indices, elem_type
            | None ->
                return! (-1, indices, Unknown),
                        make_error "Undefined identifier \"%s\"" var_name stmt.Src
        }

    if stmt.Is_Wrong then
        stmt, [stmt.Error]
    else
        let src = stmt.Src
        let stmt', errors =
            let check_expr' = check_expr sym_tab
            match stmt.Stmt' with
            | Skip -> stmt.Stmt', []
            | Assign (lhs_name,_,lhs_idcs,rhs) -> err_coll {
                let! lhs_id, lhs_idcs, lhs_type = check_arr_access sym_tab lhs_name lhs_idcs
                let! rhs = check_expr' rhs
                do! test_type'
                      "Type mismatch in assignment. The left-hand side has type %s \
                       but the right-hand side has type %s"
                      lhs_type.Str rhs.Type.Str lhs_type src rhs
                return Assign (lhs_name,lhs_id,lhs_idcs,rhs)
                }
            | If (cond,then_block,else_block) -> err_coll {
                let! cond = check_expr' cond
                let! then_block = check_stmts then_block
                let! else_block = check_stmts else_block
                do! test_type "Condition in if statement must have type bool" Bool cond
                return If (cond,then_block,else_block)
                }
            | While (cond,body) -> err_coll {
                let! cond = check_expr' cond
                let! body = check_stmts body
                do! test_type "Condition in while statement must have type bool" Bool cond
                return While (cond,body)
                }
            | Foreach (var,bound,lhs_name,lhs_id,lhs_idcs,rhs) -> err_coll {
                let! bound = check_expr' bound
                let! tmp_sym_tab = update_sym_tab_with_index_var sym_tab var
                let! lhs_id, lhs_idcs, lhs_type = check_arr_access tmp_sym_tab lhs_name lhs_idcs
                let! rhs = check_expr tmp_sym_tab rhs
                let! bnd_dims = test_type_bound "Expression must be of type bound" bound
                do! test_cond
                      "The given element has %d dimensions, but the bound at %s has %d dimensions"
                      var.Num_Dims bound.Src.Str_S bnd_dims var.Src
                      (dims_match var.Num_Dims bnd_dims)
                do! test_cond
                      "Type mismatch between left- and right-hand sides of assignment" src
                      (types_match lhs_type rhs.Type)
                return Foreach (var,bound,lhs_name,lhs_id,lhs_idcs,rhs)
                }
            | Out exprs -> err_coll {
                let! exprs = exprs |> map check_expr'
                return Out exprs
                }
        Stmt (stmt',src), errors

let check_prog (prog : Prog) : Prog * Error list =
    let prog, errors = err_coll {
        if prog.Is_Wrong then
            return! prog, [prog.Error]
        else
            let! sym_tab = update_sym_tab_with_decls (Sym_Tab []) prog.Decls
            let! stmts = map (check_stmt sym_tab) prog.Stmts
            return Prog (prog.Decls, stmts, prog.Src)
        }
    prog,
    List.sortWith (fun (a : Error) (b : Error) ->
        compare (a.Src.Start.Offset, a.Src.End.Offset)
                (b.Src.Start.Offset, b.Src.End.Offset)) errors
