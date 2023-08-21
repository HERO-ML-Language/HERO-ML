module Interpreter

open Source_Ref
open AST
open Value
open Bound

type Var_State =
    { decl : AST.Decl
      value : Value }

    member this.Decl = this.decl
    member this.Value = this.value

type State = Map<Var_ID, Var_State>

let print_state (state : State) =
    state |> Map.iter (fun _ var_state ->
        printfn "%s : %s = %s" var_state.Decl.Name var_state.Decl.Type.Str var_state.Value.Str)

let init_state_from_decls (decls : Decl list) : State =
    decls |> List.map (fun decl ->
        decl.Id, { decl = decl; value = Undef decl.Type }) |> Map.ofList

let bind_vars : State -> Decl list -> Value list -> State =
    List.fold2 (fun st decl value ->
        Map.change decl.Id (fun _ -> Some { decl = decl; value = value }) st)

let bind_index_var (state : State) (var : Index_Var) (value : Index) : State =
    bind_vars state var.Comps (List.map Int value.Comps)

// computes a default result when the evaluated parameters of an expression don't match a more
// specific rule, which happens when the values Undef, Param, and/or Error are involved
let def_result (type_ : Type) (values : Value list) =
    ((false,false,None), values)
    ||> List.fold (fun (u,p,e) value ->
        match value with
        | Undef _ -> (true,p,e)
        | Param _ -> (u,true,e)
        | Error (msg,dem,_) when e.IsNone -> (u,p,Some (msg,dem)) // save only the first error
        | _ -> (u,p,e))
    |> function
        | (_,_,Some (msg,dem)) -> Error (msg,dem,type_) // Error "wins" over the other values
        | (_,true,_) -> Param type_ // Param wins over Undef
        | (true,_,_) -> Undef type_
        // the type analysis should actually prevent the following case, but we cover it just to
        // avoid compiler warnings (and in the case of bugs)
        | (false,false,None) -> Error ("Type error", false, type_)

let rec restr_vars_by_membership (in_func : Type -> Value) (state : State) (vars : Decl list) (bound : Bound) (index : Index_Expr) : Bound =
    let num_vars = vars.Length
    let empty = Bound (num_vars, false)
    let all = Bound (num_vars, true)
    let eval_expr' = eval_expr in_func state

    // Prepares the index components `idx_comps' by recognizing those that are either constants
    // or linear polynomials in one variable, and putting them in the canonical form s * v + o,
    // where v is the variable and s and o are constants. This is returned as Some (s,v,o).
    // For other kinds of expressions, None is returned. Note that the algebraic simplifications
    // made in this function are rather simple, in the sense that if at least one sub-expression
    // is not a constant nor a linear polynomial in one variable, then None is returned for the
    // whole expression (unless a multiplication by a constant 0 occurs somewhere, which always
    // results in the constant 0 regardless of the other factor).
    let prepare_index (idx_comps : Expr list) : (int * Var_ID * int) option list =
        let rec prep (sub_expr : Expr) : (int * Var_ID * int) option =
            match eval_expr' sub_expr with
            | Int c -> Some (0,-1,c)
            | Param _ ->
                match sub_expr.Expr' with
                // direct use of variable without offset
                | Var (_,v,_) -> Some (1,v,0)
                // negated expression
                | Func_Appl (Neg_I, [arg]) ->
                    match prep arg with
                    | Some (s,v,o) -> Some (-s,v,-o)
                    | _ -> None
                // fac1 * fac2
                | Func_Appl (Mul_I, [fac1;fac2]) ->
                    let f1 = prep fac1
                    let f2 = prep fac2
                    match f1,f2 with
                    // 0 * anything = anything * 0 = 0
                    | Some (0,_,0), _ | _, Some (0,_,0) -> Some (0,-1,0)
                    // c * (s * v + o) = (s * v + o) * c = c * s * v + c * o
                    | Some (0,_,c), Some (s,v,o) | Some (s,v,o), Some (0,_,c) -> Some (c * s, v, c * o)
                    | _ -> None
                // term1 + term2 or term1 - term2
                | Func_Appl (Add_I | Sub_I as func, [term1;term2]) ->
                    let t1 = prep term1
                    let t2 =
                        match prep term2 with
                        | Some (s,v,o) when func = Sub_I -> Some (-s,v,-o)
                        | other -> other
                    match t1,t2 with
                    // (s * v + o) + c = c + (s * v + o) = s * v + (o + c)
                    | Some (s,v,o), Some (0,_,c) | Some (0,_,c), Some (s,v,o) -> Some (s,v,o + c)
                    // (f1 * v + o1) + (f2 * v + o2) = (f1 + f2) * v + (o1 + o2)
                    | Some (f1,v1,o1), Some (f2,v2,o2) when v1 = v2 -> Some (f1 + f2, v1, o1 + o2)
                    | _ -> None
                | _ -> None
            | _ ->
                // the type analysis has made sure that only integer expressions are used in
                // indices, and Undef and Error should not be possible here
                failwith ""
        idx_comps |> List.map prep

    // computes a separate bound for each variable in `vars' assuming `bound' is the product of
    // `factors' or, if factors.Length = 1, the single bound factors.Head
    let restr_sep (factors : Bound list) : Bound =
        assert (factors.Length = index.Num_Dims)
        let prep_idx = prepare_index index.Comps
        // if the index has constant components, each of them must fall inside the corresponding
        // factor of the bound, otherwise an empty bound should be returned
        let result_empty =
            (factors, prep_idx)
            ||> List.exists2 (fun fac comp ->
                match comp with
                | Some (0,_,c) -> not (fac.Contains (Index [c]))
                | _ -> false)
        if result_empty then
            empty
        else
            // compute a separate bound for each variable by considering how it occurs
            // throughout the components of the index
            vars
            |> List.map (fun var ->
                (Bound (1,true), factors, prep_idx)
                |||> List.fold2 (fun var_bnd fac comp ->
                    match comp with
                    | Some (s,v,o) when v = var.Id && s <> 0 ->
                        // The variable is used in this position of the index as s * v + o.
                        // It should therefore satisfy s * v + o ∈ fac, which is equivalent to
                        // v ∈ fac' where fac' is a bound containing the subset
                        // { (i - o) / s : i ∈ fac ∧ s | (i - o) }
                        let fac' =
                            match fac with
                            | Empty _ | All _ -> fac
                            | Dense (l,u) ->
                                // fac' = { ceil((l - o) / s) .. floor((u - o) / s) if s > 0
                                //        { ceil((u - o) / s) .. floor((l - o) / s) if s < 0
                                let l' = l - o
                                let u' = u - o
                                let t = abs s
                                let a = if l' < 0 then l'/t else (l'+t-1)/t // a = ceil(l' / t)
                                let b = if u' < 0 then (u'-t+1)/t else u'/t // b = floor(u' / t)
                                if s > 0 then Bound (a,b) else Bound (-b,-a)
                            | Sparse (_,elems,emb) ->
                                // filter out elements `i' where s doesn't divide i - o
                                let elems' =
                                    elems |> Seq.choose (fun i ->
                                        let t = i.Head - o
                                        let i' = t / s
                                        if s * i' = t then Some (Index [i']) else None)
                                Bound (1, elems', emb)
                            | Pred (_,pred_func) ->
                                Bound (1, (fun idx -> pred_func (Index [s * idx.Head + o])))
                            | Product _ ->
                                // each factor is assumed to be one-dimensional
                                failwith ""
                        meet var_bnd fac'
                    | _ -> var_bnd))
            |> function
                | [var_bnd] -> var_bnd
                | var_bnds -> Bound var_bnds

    match bound with
    // accesses in empty arrays are always out-of-bounds
    | Empty _ -> empty
    // one-dimensional bounds
    | one_dim when one_dim.Num_Dims = 1 ->
        // treat the bound as a "one-ary" product
        restr_sep [one_dim]
    // product of one-dimensional bounds
    | Product (_,factors) ->
        restr_sep factors
    // multi-dimensional sparse bound
    | Sparse (_,elems,emb) ->
        // put the index expression on a canonical form
        let prep_idx =
            List.map (fun i -> index.Comps[i]) emb // project the index onto the finite dimensions
            |> prepare_index
            |> List.indexed
        // `vars_emb' is the `emb' member of the result, and it stores the index j of
        // each variable v_j that is used in some component of the index expression as
        // s_i * v_j + o_i. (These are the only variables that can be bound by a finite
        // set.) The corresponding elements of `fst_uses' store the first position i of
        // the index expression where each variable is used. `mult_uses' gives,
        // for each variable that is used in more than one position of the index, all
        // those positions i.
        let vars_emb, fst_uses, mult_uses =
            (([],[],[]), List.indexed vars)
            ||> List.fold (fun (ve,fu,mu) (j,var) ->
                // determine all positions of the index expression where `var' is used
                let var_uses =
                    prep_idx |> List.choose (fun (i,comp) ->
                        match comp with
                        | Some (s,v,_) when v = var.Id && s <> 0 -> Some i
                        | _ -> None)
                // update output lists
                match var_uses with
                | []   -> (ve, fu, mu)                  // not used
                | [i]  -> (j::ve, i::fu, mu)            // used exactly once
                | i::_ -> (j::ve, i::fu, var_uses::mu)) // used more than once
            |> (fun (a,b,c) -> List.rev a, List.rev b, List.rev c)
        // the `elems' member of the result
        let elems'' =
            // for each element of `elems', try to turn it into an element of the result
            elems |> Seq.choose (
                Some
                // For each component ic of the index expression, if ic is constant then
                // the corresonding component ec of `elem' should equal this constant,
                // otherwise `elem' should be discarded. If ic = s * v + o then s should
                // divide ec - o. If ic is any other type of expression it is ignored.
                >> Option.filter (fun elem ->
                    (elem.Comps, prep_idx)
                    ||> List.forall2 (fun ec (_,ic) ->
                        match ic with
                        | Some (0,_,c) ->
                            c = ec
                        | Some (s,_,o) ->
                            let t = ec - o
                            t / s * s = t
                        | _ -> true))
                // for each component of the index expression on the format s * v + o,
                // apply the inverse function to the corresponding component of `elem'
                >> Option.map (fun elem ->
                    (elem.Comps, prep_idx)
                    ||> List.map2 (fun ec (_,ic) ->
                        match ic with
                        | Some (s,_,o) when s <> 0 -> (ec - o) / s
                        | _ -> ec))
                // for each variable that is used more than once throughout the index expression,
                // check that the corresponding positions of `elem'' all have identical values,
                // since otherwise `elem' should be discarded
                >> Option.filter (fun elem' ->
                    mult_uses |> List.forall (fun vu ->
                        let fst = elem'[vu.Head]
                        vu.Tail |> List.forall (fun i -> elem'[i] = fst)))
                // permute/project `elem''
                >> Option.map (fun elem' -> fst_uses |> List.map (fun i -> elem'[i]) |> Index))
        Bound (num_vars, elems'', vars_emb)
    // multi-dimensional predicate bound
    | Pred (_,pred_func) ->
        // predicate function to test candidate assignments of the variables in `vars'
        let vars_pred_func (var_vals : Index) : bool =
            // temporarily bind the variables in `vars' to the values in `var_vals', then
            // evaluate the index used in the considered array access (`index') and see if the
            // array is defined for that index
            let tmp_state = bind_vars state vars (List.map Int var_vals.Comps)
            match eval_index_expr in_func tmp_state index with
            | Value.Index ev_idx -> pred_func ev_idx
            // if the predicate evaluates to Undef, Param, or ERROR, we go with the
            // most conservative approach and return true (TODO)
            | _ -> true
        Bound (num_vars, vars_pred_func)
    | _ -> all

and restr_vars_by_forall (in_func : Type -> Value) (state : State) (vars : Decl list) (body : Expr) : Value =
    let num_vars = vars.Length
    let type_ = Type.Bound num_vars
    let empty = Bound (num_vars, false)
    let all = Bound (num_vars, true)

    // Traverses the `body' expression tree. The main work horse of the function.
    let rec restr (t_or_f : bool option) (sub_expr : Expr) : Bound =
        assert (t_or_f.IsNone || sub_expr.Type = Type.Bool)

        let eval_expr' = eval_expr in_func state
        let eval_bound_func' = eval_bound_func in_func state
        let restr' = restr t_or_f
        let restr_t = restr (Some true)
        let restr_f = restr (Some false)
        let restr_n = restr None

        // restrict the variables by recursively considering the sub-trees (with special
        // consideration of non-strict operators). If the current sub-expression is an array access,
        // then further restrict the variables based on the bound of the accessed array
        match sub_expr.Expr' with
        | Array_Access (array,index) ->
            let bnd1 = array :: index.Comps |> List.map restr_n |> List.fold meet all
            let bnd2 =
                match eval_bound_func' array with
                | Bound arr_bound ->
                    restr_vars_by_membership in_func state vars arr_bound index
                | _ ->
                    all
            meet bnd1 bnd2
        | Dense_Bound (l,u) ->
            match eval_expr' l, eval_expr' u with
            | Int _, Int _ -> all // constant endpoints. TODO: This should be generalized to when l and u don't depend on `vars'
            | _ ->
                // recurse into both endpoints
                let bnd_l = restr_n l
                let bnd_u = restr_n u
                // predicate bound that ensures l ≤ u
                let bnd_lu =
                    let pred_func (index : Index) =
                        let tmp_state = bind_vars state vars (List.map Int index.Comps)
                        match eval_expr in_func tmp_state l,
                              eval_expr in_func tmp_state u with
                        | Int ev_l, Int ev_u -> ev_l <= ev_u
                        | (Undef _ | Error _), (Undef _ | Error _) -> false
                        | _ -> true
                    Bound (num_vars, pred_func)
                bnd_l |>meet<| bnd_u |>meet<| bnd_lu
        | Dense_Array (bound, _) ->
            // only consider the expression(s) for the bound
            bound
            |> List.collect (fun (a,b,d) ->
                match b with
                | None -> [restr_n a]
                | Some b' ->
                    match eval_expr' a, eval_expr' b' with
                    | Int _, Int _ -> [] // constant endpoints. TODO: This should be generalized to when a and b' don't depend on `vars'
                    | _ ->
                        let bnd_a = restr_n a
                        let bnd_b = restr_n b'
                        // include an additional bound to ensure a + d = b. This is handled
                        // equivalently to an array access A[b - a] where bound(A) = d..d
                        // TODO: We should define a function in Source_Ref to create dummy source refs
                        // instead of using sub_expr.Src
                        let ``b - a`` = Index_Expr ([ Expr (Func_Appl (Func.Sub_I, [b';a]), sub_expr.Src) ], sub_expr.Src)
                        let ``d..d`` = Bound (d,d)
                        let bnd_ab = restr_vars_by_membership in_func state vars ``d..d`` ``b - a``
                        [bnd_a; bnd_b; bnd_ab])
            |> List.fold meet all
        | Sparse_Array (indices, _) ->
            // only recurse into the expression(s) for the indices (bound)
            indices
            |> List.collect (fun idx -> List.map restr_n idx.Comps)
            |> List.fold meet all
        | Array_Compr (_,_, bound) ->
            // only recurse into the bound expression
            restr_n bound
        | Forall (_, elem_expr) ->
            // TODO: not consistent with the other rules for array expressions, which don't
            // traverse the expression(s) for the elements
            restr_n elem_expr
        // B(if(cond, arg2, arg3)) = (B_t(cond) ⊓ B(arg2)) ⊔ (B_f(cond) ⊓ B(arg3)),
        // B_t(if(cond, arg2, arg3)) = (B_t(cond) ⊓ B_t(arg2)) ⊔ (B_f(cond) ⊓ B_t(arg3)),
        // B_f(if(cond, arg2, arg3)) = (B_t(cond) ⊓ B_f(arg2)) ⊔ (B_f(cond) ⊓ B_f(arg3))
        | Func_Appl (Func.If _, [cond;arg2;arg3]) ->
            ((restr_t cond) |>meet<| (restr' arg2)) |>join<| ((restr_f cond) |>meet<| (restr' arg3))

        // && and ||
        | Func_Appl (And | Or as func, [arg1;arg2]) ->
            match t_or_f with
            // B_t(arg1 && arg2) = B_t(arg1) ⊓ B_t(arg2)
            // B_f(arg1 || arg2) = B_f(arg1) ⊓ B_f(arg2)
            | Some t_or_f' when t_or_f' = (func = And) ->
                (restr' arg1) |>meet<| (restr' arg2)
            // B(arg1 && arg2) = B_f(arg1) ⊔ (B_t(arg1) ⊓ B(arg2))
            // B(arg1 || arg2) = B_t(arg1) ⊔ (B_f(arg1) ⊓ B(arg2))
            // B_f(arg1 && arg2) = B_f(arg1) ⊔ (B_t(arg1) ⊓ B_f(arg2))
            // B_t(arg1 || arg2) = B_t(arg1) ⊔ (B_f(arg1) ⊓ B_t(arg2))
            | _ ->
                // here t_or_f = None or t_or_f = Some (func = Or)
                let restr_a = restr (Some (func = And))
                let restr_o = restr (Some (func = Or))
                (restr_o arg1) |>join<| ((restr_a arg1) |>meet<| (restr' arg2))

        // B_t(true) = B_f(false) = all,
        // B_t(false) = B_f(true) = empty,
        // B_t(sub_expr) = B_f(sub_expr) = B(sub_expr) for non-constant sub_expr
        | _ when t_or_f.IsSome ->
            match eval_expr' sub_expr with
            | Bool b -> if b = t_or_f.Value then all else empty
            | Param _ -> restr_n sub_expr
            | _ -> failwith ""
        | _ ->
            // recurse into all child expressions
            get_child_exprs sub_expr |> List.map restr_n |> List.fold meet all

    match eval_expr in_func state body with
    | Param _ -> Value.Bound (restr None body)
    | Undef _ -> Undef type_
    | Error (msg,dem,_) -> Error (msg,dem,type_)
    | _ -> Value.Bound all

// evaluates bound(arr_expr)
and eval_bound_func (in_func : Type -> Value) (state : State) (arr_expr : Expr) : Value =
    let eval_expr' = eval_expr in_func state
    let eval_index_expr' = eval_index_expr in_func state
    let eval_bound_func' = eval_bound_func in_func state
    let type_ =
        match arr_expr.Type with
        | Type.Array (_,num_dims) -> Type.Bound num_dims
        | _ -> failwith ""
    match arr_expr.Expr' with
    | Dense_Array (bound,_) ->
        let fac_type = Type.Bound 1
        bound
        |> List.map (fun (a,b,d) ->
            match eval_expr' a,
                  Option.map eval_expr' b with
            | Int ev_a, None ->
                let ev_a' = ev_a + d
                Value.Bound (Bound (min ev_a ev_a', max ev_a ev_a'))
            | Int ev_a, Some (Int ev_b) when ev_b = ev_a + d ->
                let ev_a' = ev_a + d
                Value.Bound (Bound (min ev_a ev_a', max ev_a ev_a'))
            | Int ev_a, Some (Int ev_b) when ev_b < ev_a ->
                let range_src = Source_Ref.merge a.Src b.Value.Src
                let msg =
                    sprintf "%s evaluates to the range %d..%d, which is invalid since \
                             the first endpoint must be less than or equal to the second endpoint"
                        range_src.Text ev_a ev_b
                Error (msg,false,fac_type)
            | Int ev_a, Some (Int ev_b) ->
                // ev_a ≤ ev_b but ev_b ≠ ev_a + d
                let range_src = Source_Ref.merge a.Src b.Value.Src
                let msg =
                    sprintf "%s evaluates to the range %d..%d, which spans %d indices \
                             as opposed to %d indices as specified by the array elements"
                        range_src.Text ev_a ev_b (ev_b-ev_a+1) (d+1)
                Error (msg,false,fac_type)
            | _1,_2 ->
                def_result fac_type (_1 :: Option.toList _2))
        |> function
            | Bound_List [ev_fac] -> Value.Bound ev_fac
            | Bound_List ev_facs  -> Value.Bound (Bound ev_facs)
            | _1 -> def_result type_ _1
    | Sparse_Array (indices,_) ->
        match List.map eval_index_expr' indices with
        | Index_List ev_idcs -> Value.Bound (Bound ev_idcs)
        | _1 -> def_result type_ (List.concat _1)
    | Array_Compr (_, _, bound) ->
        eval_expr' bound
    | Forall (var, elem_expr) ->
        restr_vars_by_forall in_func state var.Comps elem_expr
    | Func_Appl (Slice_Array _, [arg1;arg2]) ->
        match eval_bound_func' arg1,
              eval_expr' arg2 with
        | Bound bnd1, Bound bnd2 -> Value.Bound (bnd1 |>meet<| bnd2)
        | _1,_2 -> def_result type_ [_1;_2]
    | HO_Func_Appl (Scan _, _, arr_arg) ->
        eval_bound_func' arr_arg
    | _ ->
        match eval_expr' arr_expr with
        | Array ev_arr -> Value.Bound ev_arr.Bound
        | _1 -> def_result type_ [_1]

and eval_expr (in_func : Type -> Value) (state : State) (expr : Expr) : Value =
    let eval_expr' = eval_expr in_func state
    let eval_index_expr' = eval_index_expr in_func state
    let eval_bound_func' = eval_bound_func in_func state
    let def_result' = def_result expr.Type

    let (|Match|) param _ = param

    // Note: Here op is assumed to be of type Int x Int -> Int, Float x Float -> Float,
    // Bool x Bool -> Bool, and so on. These cases have been lifted out into a separate function
    // because they are valid arguments to scan() and reduce(), and we want to reuse the same logic
    // when evaluating those functions.
    let bin_op (op : Func) =
        match op with
        | Add_I   & Match (+)   iop
        | Sub_I   & Match (-)   iop
        | Mul_I   & Match (*)   iop
        | Div_I   & Match (/)   iop
        | Mod     & Match (%)   iop
        | L_Shift & Match (<<<) iop
        | R_Shift & Match (>>>) iop ->
            fun (arg1 : Value) (arg2 : Value) ->
                match arg1, arg2 with
                | Int _, Int 0 when op = Div_I || op = Mod -> Error ("Division by zero", false, Type.Int)
                // experimental: bit shifts by negative amounts reverse the shift direction
                | Int arg1', Int arg2' when op = L_Shift && arg2' < 0 -> Int (arg1' >>> -arg2')
                | Int arg1', Int arg2' when op = R_Shift && arg2' < 0 -> Int (arg1' <<< -arg2')
                | Int arg1', Int arg2' -> Int (arg1' |>iop<| arg2')
                | _ -> def_result Type.Int [arg1;arg2]
        | Add_F & Match (+) fop
        | Sub_F & Match (-) fop
        | Mul_F & Match (*) fop
        | Div_F & Match (/) fop ->
            fun (arg1 : Value) (arg2 : Value) ->
                match arg1, arg2 with
                | Float arg1', Float arg2' -> Float (arg1' |>fop<| arg2')
                | _ -> def_result Type.Float [arg1;arg2]
        | And & Match (&&) bop
        | Or  & Match (||) bop ->
            fun (arg1 : Value) (arg2 : Value) ->
                match arg1, arg2 with
                | Bool arg1', Bool arg2' -> Bool (arg1' |>bop<| arg2')
                | _ -> def_result Type.Bool [arg1;arg2]
        | Join num_dims & Match join bop
        | Meet num_dims & Match meet bop ->
            fun (arg1 : Value) (arg2 : Value) ->
                match arg1, arg2 with
                | Bound arg1', Bound arg2' -> Value.Bound (arg1' |>bop<| arg2')
                | _ -> def_result (Type.Bound num_dims) [arg1;arg2]
        | _ -> failwith ""

    match expr.Expr' with
    // leafs in the expression tree ----------------------------------------------------
    | Undef_Const type_  -> Undef type_
    | Error_Const type_  -> Error ("(ERROR constant)", false, type_)
    | Int_Const value    -> Int value
    | Float_Const value  -> Float value
    | Bool_Const value   -> Bool value
    | Bound_Const is_all -> Value.Bound (Bound (0,is_all))
    | Var (_,id,_) ->
        match Map.tryFind id state with
        | Some var -> var.Value
        | None -> Param expr.Type // depends on a free variable
    | In type_ -> in_func type_

    // array access
    | Array_Access (array,index) ->
        match eval_expr' array,
              eval_index_expr' index with
        | Array ev_arr, Value.Index ev_idx -> ev_arr.Access ev_idx
        | _1,_2 -> def_result' (_1::_2)

    // bounds -----------------------------------------------------------------------------
    | Dense_Bound (l,u) ->
        match eval_expr' l, eval_expr' u with
        | Int ev_l, Int ev_u -> Value.Bound (Bound (ev_l,ev_u))
        | _1,_2 -> def_result' [_1;_2]
    | Sparse_Bound elems ->
        match List.map eval_index_expr' elems with
        | Index_List ev_elems -> Value.Bound (Bound (elems.Head.Num_Dims, ev_elems))
        | _1 -> def_result' (List.concat _1)
    | Pred_Bound (var,pred) ->
        let pred_func index =
            let tmp_state = bind_index_var state var index
            eval_expr in_func tmp_state pred = Bool true
        Value.Bound (Bound (var.Num_Dims, pred_func))

    // arrays -----------------------------------------------------------------
    | Dense_Array (_,elems)
    | Sparse_Array (_,elems) ->
        match eval_bound_func' expr with
        | Bound ev_bnd ->
            let ev_elems = elems |> List.map eval_expr'
            match expr.Expr' with
            | Dense_Array _ ->
                Array (Abst_Array (elems.Head.Type, ev_bnd, ev_elems |> Array.ofList))
            | _ -> // Sparse_Array
                Array (Abst_Array (elems.Head.Type, Seq.zip ev_bnd.Get_Seq ev_elems))
        | _1 ->
            def_result' [_1]
    | Array_Compr (var,elem_expr,_)
    | Forall (var,elem_expr) ->
        match eval_bound_func' expr with
        | Bound ev_bnd ->
            let elem_func index =
                let tmp_state = bind_index_var state var index
                eval_expr in_func tmp_state elem_expr
            match expr.Expr' with
            | Array_Compr _ ->
                Array (Abst_Array (elem_expr.Type, ev_bnd, elem_func))
            | _ -> // Forall
                let demote_errors = function Error (_,true,t) -> Undef t | other -> other
                Array (Abst_Array (elem_expr.Type, ev_bnd, elem_func >> demote_errors))
        | _1 -> def_result' [_1]

    // function applications --------------------------------------------------------------------
    | Func_Appl (func,args) ->
            let ev_args =
                match func with
                // non-strict functions
                | Func.If _ | And | Or -> [eval_expr' args[0]]
                | Func.Bound _ -> []
                // evaluate all arguments to strict functions
                | _ -> List.map eval_expr' args
            match func, ev_args with
            | Func.If _, [Bool true]  -> eval_expr' args[1]
            | Func.If _, [Bool false] -> eval_expr' args[2]
            | Is_Def _, [Undef _] -> Bool false
            | Is_Def _, [Param _ | Error _] -> def_result' ev_args
            | Is_Def _, _ -> Bool true
            | Cast_F_I, [Float arg] -> Int (int arg)
            | Cast_I_F, [Int arg] -> Float (float arg)
            | Neg_I, [Int arg] -> Int -arg
            | Neg_F, [Float arg] -> Float -arg
            | Exp, [Float arg] -> Float (exp arg)
            | Sqrt, [Float arg] -> Float (sqrt arg)
            | (Add_I | Sub_I | Mul_I | Div_I | Mod | L_Shift | R_Shift), [Int _; Int _]
            | (Add_F | Sub_F | Mul_F | Div_F), [Float _; Float _] ->
                bin_op func ev_args[0] ev_args[1]
            | ( LT_I & Match (<)  iop
              | LE_I & Match (<=) iop
              | GE_I & Match (>=) iop
              | GT_I & Match (>)  iop
              | Eq_I & Match (=)  iop
              | NE_I & Match (<>) iop), [Int arg1; Int arg2] ->
                Bool (arg1 |>iop<| arg2)
            | ( LT_F & Match (<)  fop
              | LE_F & Match (<=) fop
              | GE_F & Match (>=) fop
              | GT_F & Match (>)  fop
              | Eq_F & Match (=)  fop
              | NE_F & Match (<>) fop), [Float arg1; Float arg2] ->
                Bool (arg1 |>fop<| arg2)
            | ( Eq_B & Match (=)  bop
              | NE_B & Match (<>) bop), [Bool arg1; Bool arg2] ->
                Bool (arg1 |>bop<| arg2)
            | Not, [Bool arg] -> Bool (not arg)
            | And, [Bool false] | Or, [Bool true] -> ev_args.Head
            | And, [Bool true] | Or, [Bool false] -> eval_expr' args[1]
            | Size _, [Bound (Finite bnd)] -> Int bnd.Size
            | Size _, [Bound (Infinite _)] -> Error (sprintf "%s cannot be applied to infinite bounds" func.Str_P, false, Type.Int)
            | Is_Finite _,    [Bound (Finite _)]
            | Is_Dense _,     [Bound (Dense _)]
            | Is_Sparse _,    [Bound (Sparse _)]
            | Is_Predicate _, [Bound (Pred _)]
            | Is_Product _,   [Bound (Product _)] ->
                Bool true
            | (Is_Finite _ | Is_Dense _ | Is_Sparse _ | Is_Predicate _ | Is_Product _), [Bound _] ->
                Bool false
            | Join _, [Bound arg1; Bound arg2] ->
                Value.Bound (arg1 |>join<| arg2)
            | Meet _, [Bound arg1; Bound arg2] ->
                Value.Bound (arg1 |>meet<| arg2)
            | Bound_Prod _, Bound_List facs ->
                let facs' = facs |> List.map (
                    function
                    // "empty" and "all" with "0 dimensions" become one-dimensional when
                    // used as factors
                    | Empty 0 -> Empty_1
                    | All   0 -> All_1
                    | other -> other)
                Value.Bound (Bound facs')
            | Func.Bound _, [] ->
                eval_bound_func' args.Head
            | Slice_Array _, [Array arr; Bound bnd] ->
                Array (arr.Slice bnd)
            | _ ->
                def_result' ev_args
    | Member_Func_Appl (_,index_arg,bound_arg) ->
        match eval_index_expr' index_arg,
              eval_expr' bound_arg with
        | Value.Index ev_idx, Bound ev_bnd -> Bool (ev_bnd.Contains ev_idx)
        | _1,_2 -> def_result' (_2::_1)
    | HO_Func_Appl (func, func_arg, arr_arg) ->
        match (eval_expr' arr_arg).Tabulate with
        | Array ev_arr_arg ->
            // elements that are Undef should be ignored
            let elems = ev_arr_arg.Get_Seq |> Seq.filter (snd >> function Undef _ -> false | _ -> true) |> Seq.cache
            let bin_op' = bin_op func_arg
            match func with
            | Reduce _ ->
                if Seq.isEmpty elems then
                    Error (sprintf "%s requires that the array has at least one defined element" func.Str_P, false, expr.Type)
                else
                    elems |> Seq.map snd |> Seq.reduce bin_op'
            | Scan _ ->
                if Seq.isEmpty elems then
                    // empty arrays and arrays containing only Undefs are just copied
                    Array ev_arr_arg
                else
                    let out_elems =
                        (Seq.head elems, Seq.tail elems)
                        ||> Seq.scan (fun (_,acc) (i,v) -> i, bin_op' acc v)
                        |> Seq.cache
                    // reuse the input array but overwrite its non-Undef values
                    Array (ev_arr_arg.Update_Many out_elems)
        | _1 -> def_result' [_1]

and eval_index_expr (in_func : Type -> Value) (state : State) (index_expr : Index_Expr) =
    index_expr.Comps |> List.map (eval_expr in_func state)

let update_state (lval_var : Var_ID) (state : State) (lval_indices : Index list) (rval : Value) : State =
    // recursively index the array (where we view a scalar as a 0-dimensional array) and update it
    let rec update_array (value : Value) (indices : Index list) : Value =
        match value, indices with
        | _, [] -> rval // no more levels of indexing; store the r-value
        | Array arr, idx::tail ->
            match arr.Access idx with
            | Error (msg,_,_) -> failwith msg
            | old_elem ->
                let new_elem = update_array old_elem tail
                Array (arr.Update idx new_elem)
        | Undef _, _ -> failwith "Access of uninitialized array" // TODO: Perhaps this could be due to other reasons as well?
        | _ -> failwith "Only arrays can be indexed"

    Map.change lval_var (
        function
        | Some var_state ->
            let old_val = var_state.Value
            let new_val = update_array old_val lval_indices
            Some { var_state with value = new_val }
        | None ->
            failwithf "Undefined variable %d" lval_var) state

let rec execute_stmt (in_func : Type -> Value) (out_func : Expr -> Value -> unit) (state : State) (stmt : Stmt) : State =
    let execute_stmts = List.fold (execute_stmt in_func out_func) state
    let eval_expr' = eval_expr in_func state
    let eval_index_expr' = eval_index_expr in_func state
    let fail' msg (src : Source_Ref) = failwithf "%s: %s" src.Str_S msg
    let fail msg (node : Node) = fail' msg node.Src
    let eval_rhs state' rhs =
        match (eval_expr in_func state' rhs).Tabulate with
        | Error (msg,_,_) -> fail msg rhs
        | other -> other
    match stmt.Stmt' with
    | Skip -> state
    | Assign (_,lhs_id,lhs_indices,rhs) ->
        match List.map eval_index_expr' lhs_indices with
        | Index_List lval_idcs ->
            let rval = eval_rhs state rhs
            update_state lhs_id state lval_idcs rval
        | _ ->
            fail' "One or more indices could not be evaluated" (
                (Source_Ref.merge (List.head lhs_indices).Src (List.last lhs_indices).Src))
    | If (cond,then_block,else_block) ->
        match eval_expr' cond with
        | Bool ev_cond ->
            execute_stmts (if ev_cond then then_block else else_block)
        | Error (msg,_,_) -> fail msg cond
        | _ -> fail "Condition evaluated to an undefined value" cond
    | While (cond,body) ->
        match eval_expr' cond with
        | Bool true ->
            execute_stmts body |> execute_stmt in_func out_func <| stmt
        | Bool false ->
            state
        | Error (msg,_,_) -> fail msg cond
        | _ -> fail "Condition evaluated to an undefined value" cond
    | Foreach (var,bound,lhs_name,lhs_id,lhs_indices,rhs) ->
        // create a dummy expression representing the LHS as an array access (i.e., as a read).
        // This is to be able to apply the restriction mechanism on it
        // TODO: This might not be correct if the array being assigned to contains Undefs. The
        // indices of these elements might be filtered out by the restriction, even though they
        // point to valid positions to write to in the array.
        let lhs_as_access =
            let type_ = // look up the array type
                match Map.tryFind lhs_id state with
                | Some { decl = decl; value = _ } -> decl.Type
                | None -> failwith ""
            let src = stmt.Src // dummy source reference
            (Expr (Var (lhs_name, lhs_id, type_), src), lhs_indices)
            ||> List.fold (fun arr_expr index -> Expr (Array_Access (arr_expr, index), src))
        match eval_expr' bound,
              restr_vars_by_forall in_func state var.Comps lhs_as_access,
              restr_vars_by_forall in_func state var.Comps rhs with
        | Bound expl_bnd, Bound lhs_bnd, Bound rhs_bnd ->
            let lr_pairs =
                let combined_bnd =
                    match expl_bnd |>meet<| lhs_bnd |>meet<| rhs_bnd with
                    | Finite fin -> fin
                    | Infinite _ -> fail "Infinite bound in foreach statement" stmt
                combined_bnd.Get_Seq
                |> Seq.map (fun idx ->
                    let tmp_state = bind_index_var state var idx
                    match List.map (eval_index_expr in_func tmp_state) lhs_indices with
                    | Index_List lval_idcs ->
                        let rval = eval_rhs tmp_state rhs
                        (lval_idcs, rval)
                    | _ ->
                        fail' "One or more indices could not be evaluated" (
                            (Source_Ref.merge (List.head lhs_indices).Src (List.last lhs_indices).Src)))
            (state, lr_pairs)
            ||> Seq.fold (fun state (lval_idcs,rval) ->
                update_state lhs_id state lval_idcs rval)
        | Error (msg,_,_), _, _ -> fail msg bound
        | _, Error (msg,_,_), _ -> fail msg lhs_as_access
        | _, _, Error (msg,_,_) -> fail msg rhs
        | _, _, _ -> fail "Bound of foreach expression evaluated to an undefined value" stmt
    | Out exprs ->
        if exprs.IsEmpty then printfn ""
        else List.iter (fun expr -> out_func expr (eval_expr' expr)) exprs
        state

let execute_prog (in_func : Type -> Value) (out_func : Expr -> Value -> unit) (prog : Prog) : State =
    (init_state_from_decls prog.Decls, prog.Stmts)
    ||> List.fold (execute_stmt in_func out_func)
