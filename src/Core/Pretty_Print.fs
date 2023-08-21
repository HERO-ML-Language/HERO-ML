module Pretty_Print

open AST
open System.Text

let PP_list (put : string -> unit) (pp_func : (string -> unit) -> 'T -> unit) (sep : string) (elems : 'T list) =
    if not elems.IsEmpty then
        pp_func put elems.Head
        elems.Tail |> List.iter (fun e -> put sep; pp_func put e)

let PP_pared_list (put : string -> unit) (pp_func : (string -> unit) -> 'T -> unit) (sep : string) (elems : 'T list) =
    if not elems.IsEmpty then
        let put_pars = not elems.Tail.IsEmpty
        if put_pars then put "("
        PP_list put pp_func sep elems
        if put_pars then put ")"

let PP_Decl (put : string -> unit) (decl : Decl) =
    List.iter put [ decl.Name; " : "; decl.Type.Str; "\n" ]

let PP_Index_Var (put : string -> unit) (var : Index_Var) =
    var.Comps |> PP_pared_list put (fun _ decl -> put decl.Name) ","

let rec PP_Expr (pars : bool) (put : string -> unit) (expr : Expr) =
    if expr.Is_Wrong then put "[erroneous expression]"
    else
        let put_pars = pars && (
            match expr.Expr' with
            | Func_Appl (func,_) ->
                match func with
                // infix numeric operators
                | Add_I | Sub_I | Mul_I | Div_I | Mod
                | Add_F | Sub_F | Mul_F | Div_F
                | LT_I | LE_I | GE_I | GT_I
                | LT_F | LE_F | GE_F | GT_F
                | Eq_I | NE_I
                | Eq_F | NE_F
                | Eq_B | NE_B
                // boolean operators
                | And | Or
                // arr|bnd
                | Slice_Array _ -> true
                | _ -> false
            | _ -> false)
        if put_pars then put "("
        match expr.Expr' with
        | Undef_Const _ -> put "?"
        | Error_Const _ -> put "ERROR"
        | Int_Const i        -> put (i.ToString ())
        | Float_Const f      -> put (f.ToString ())
        | Bool_Const b       -> put (if b then "true" else "false")
        | Bound_Const is_all -> put (if is_all then "all" else "empty")
        | Var (name,_,_)    -> put name
        //| Var (name,id,_)   -> put name; put " ("; put (id.ToString ()); put ")"
        | In t -> put "in "; put t.Str
        | Array_Access (array,index) -> PP_Expr_P put array; PP_Array_Access put index
        // bounds
        | Dense_Bound (l,u) ->
            PP_Expr_P put l; put ".."; PP_Expr_P put u
        | Sparse_Bound elems ->
            put "{ "; PP_list put PP_Index_Expr ", " elems; put " }"
        | Pred_Bound (var,pred) ->
            put "{ "; PP_Index_Var put var; put " : "; PP_Expr_N put pred; put " }"
        // arrays
        | Dense_Array (bound,elems) ->
            let put_range _ (a : Expr, b : Expr option, d : int) =
                if b.IsSome then
                    PP_Expr_P put a; put ".."; PP_Expr_P put b.Value
                else
                    (if d >= 0 then PP_Expr_P put a); put ".."; (if d < 0 then PP_Expr_P put a)
            put "[ "; PP_pared_list put put_range "," bound; put " : "
            let widths = bound |> List.map (fun (_,_,d) -> (abs d) + 1) |> List.rev
            let wh,wt = widths.Head, widths.Tail
            let rows = List.chunkBySize wh elems
            (wt,rows) ||> List.fold (fun ctr row ->
                PP_Expr_List put ", " row
                match List.tryFindIndex ((<>) 1) ctr with
                | Some k ->
                    put (String.replicate (k+1) ";"); put " "
                    let b = List.skip k ctr
                    (List.take k wt) @ ((b.Head - 1) :: b.Tail)
                | None -> []
            ) |> ignore
            put " ]"
        | Sparse_Array (indices,elems) ->
            put "[ "
            PP_list put (fun _ (index,elem) ->
                PP_Index_Expr put index; put ":"; PP_Expr_N put elem) ", " (List.zip indices elems)
            put " ]"
        | Array_Compr (var,elem_expr,bound) ->
            put "[ "; PP_Expr_N put elem_expr; put " : "
            PP_Index_Var put var; put " in "; PP_Expr_N put bound; put " ]"
        | Forall(var,expr) ->
            put "forall "; PP_Index_Var put var; put " -> "; PP_Expr_N put expr; put ")"
        | Func_Appl(func,args) ->
            match func with
            | Func.If _
            | Is_Def _
            | Cast_F_I
            | Cast_I_F
            | Exp
            | Sqrt
            | Not
            | Size _
            | Is_Finite _ | Is_Dense _ | Is_Sparse _ | Is_Predicate _ | Is_Product _
            | Join _ | Meet _
            | Bound _ ->
                put func.Str; put "("; PP_Expr_List put "," args; put ")"
            | Neg_I | Neg_F ->
                 put "-"; PP_Expr_P put args[0]
            | Add_I | Sub_I | Mul_I | Div_I | Mod
            | Add_F | Sub_F | Mul_F | Div_F
            | L_Shift | R_Shift
            | LT_I | LE_I | GE_I | GT_I
            | LT_F | LE_F | GE_F | GT_F
            | Eq_I | NE_I
            | Eq_F | NE_F
            | Eq_B | NE_B
            | And | Or
            | Slice_Array _ ->
                PP_Expr_P put args[0]; put " "; put func.Str; put " "; PP_Expr_P put args[1]
            | Bound_Prod _ ->
                put "("; PP_Expr_List put "," args; put ")"
        | Member_Func_Appl (_,index_arg,bound_arg) ->
            put "member("; PP_Index_Expr put index_arg; put ","; PP_Expr_N put bound_arg; put ")"
        | HO_Func_Appl (func,func_arg,arg) ->
            put func.Str; put "("; put func_arg.Str; put ", "; PP_Expr_N put arg; put ")"
        if put_pars then put ")"

and PP_Expr_P = PP_Expr true
and PP_Expr_N = PP_Expr false

and PP_Expr_List (put : string -> unit) = PP_list put PP_Expr_N

and PP_Index_Expr (put : string -> unit) (index : Index_Expr) =
    PP_pared_list put PP_Expr_N "," index.Comps

and PP_Array_Access (put : string -> unit) (index : Index_Expr) =
    put "["; PP_Expr_List put "," index.Comps; put "]"

let rec PP_Stmt (put : string -> unit) (ind : string) (stmt  : Stmt) =
    put ind
    if stmt.Is_Wrong
    then put "[erroneous statement]"
    else
        match stmt.Stmt' with
        | Skip -> put "skip"
        | Assign (lhs_name,_,lhs_idcs,rhs) ->
            put lhs_name
            lhs_idcs |> List.iter (PP_Array_Access put)
            put " = "
            PP_Expr_N put rhs
        | If (cond,then_block,else_block) ->
            put "if ("
            PP_Expr_N put cond
            put ")\n"
            then_block |> List.iter (PP_Stmt put (ind + "    "))
            if not else_block.IsEmpty then
                put "\nelse\n"
                else_block |> List.iter (PP_Stmt put (ind + "    "))
        | While (cond,block) ->
            put "while ("
            PP_Expr_N put cond
            put ") do\n"
            block |> List.iter (PP_Stmt put (ind + "    "))
        | Foreach (var,bound,lhs_name,_,lhs_idcs,rhs) ->
            put "foreach "
            PP_Index_Var put var
            put " in "
            PP_Expr_N put bound
            put " do "
            put lhs_name
            lhs_idcs |> List.iter (PP_Array_Access put)
            put " = "
            PP_Expr_N put rhs
        | Out exprs ->
            put "out "
            PP_Expr_List put ", " exprs
    put "\n"

let Pretty_Print (prog : Prog) : string =
    let sb = StringBuilder 1000
    let put (str : string) = sb.Append str |> ignore
    prog.Decls |> List.iter (PP_Decl put)
    prog.Stmts |> List.iter (PP_Stmt put "")
    sb.ToString ()
