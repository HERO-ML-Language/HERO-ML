module Tests_Common

open Xunit

open Parser_Wrapper
open Value
open Bound
open Interpreter

let in_func (_ : AST.Type) : Value = failwith "\"in\" expressions are not supported in tests"

let run_program (src : string) : State =
    let prog, errors = Parse_From_String_Ext src
    Assert.Empty(errors)
    Assert.True(prog.IsSome)
    Interpreter.execute_prog in_func (fun _ _ -> ()) prog.Value

let eval_expr (context : string) (expr : string) : Value =
    let prog_src = sprintf "%s\nout %s" context expr
    let prog, errors = Parse_From_String_Ext prog_src
    Assert.Empty(errors)
    Assert.True(prog.IsSome)
    let mutable ev_expr : Value option = None
    Interpreter.execute_prog in_func (fun _ value -> ev_expr <- Some value) prog.Value |> ignore
    ev_expr.Value

let eval_expr_int   ctx expr = match eval_expr ctx expr with Int v   -> v | _ -> failwith ""
let eval_expr_float ctx expr = match eval_expr ctx expr with Float v -> v | _ -> failwith ""
let eval_expr_bool  ctx expr = match eval_expr ctx expr with Bool v  -> v | _ -> failwith ""
let eval_expr_Bound ctx expr = match eval_expr ctx expr with Bound v -> v | _ -> failwith ""
let eval_expr_Array ctx expr = match eval_expr ctx expr with Array v -> v | _ -> failwith ""

let T_to_Value (value : 'T) : Value =
    match box value with
    | :? int as i -> Int i
    | :? float as f -> Float f
    | :? bool as b -> Bool b
    | :? Bound as b -> Value.Bound b
    | :? Abst_Array as a -> Array a
    | :? Value as v -> match v with Error (_,dem,t) -> Error ("",dem,t) | v' -> v'
    | _ -> failwith "" // to silence compiler warning

let check_expr_ctx (context : string) (expr : string) (exp_value : 'T) =
    let exp_value' = T_to_Value exp_value
    let result = 
        match eval_expr context expr with
        | Error (_,dem,t) -> Error ("",dem,t) // remove message so it's not compared
        | other -> other
    Assert.Equal(exp_value', result)

let check_expr (expr : string) (exp_value : 'T) = check_expr_ctx "" expr exp_value

let array_dense (index_ranges : (int * int) list) (elems : 'T array) =
    let bound =
        if index_ranges.Tail.IsEmpty
        then Bound index_ranges.Head
        else Bound index_ranges
    let elems' = Array.map T_to_Value elems
    let elem_type = elems'[0].Type
    Abst_Array (elem_type, bound, elems')

let array_dense_1d_0 (elems : 'T array) = array_dense [(0,elems.Length-1)] elems

let array_sparse (elems : (int list * 'T) seq) =
    let elems' = Seq.map (fun (i,v) -> Index i, T_to_Value v) elems
    let elem_type = (snd (Seq.head elems')).Type
    Abst_Array (elem_type, elems')

let array_sparse_1d (elems : (int * 'T) seq) =
    let elems' = Seq.map (fun (i,v) -> [i],v) elems
    array_sparse elems'

let gen_indices_1 (a1,b1) : Index seq =
    seq { for i in a1..b1 -> Index [i] }

let gen_indices_2 (a1,b1) r2 : Index seq =
    ({ a1..b1 }, gen_indices_1 r2)
    ||> Seq.allPairs
    |> Seq.map (fun (i1,i2) -> Index (i1::i2.Comps))

let gen_indices_3 (a1,b1) r2 r3 : Index seq =
    ({ a1..b1 }, gen_indices_2 r2 r3)
    ||> Seq.allPairs
    |> Seq.map (fun (i1,i23) -> Index (i1::i23.Comps))
