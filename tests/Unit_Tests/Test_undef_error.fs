module Test_undef_error

open Xunit
open Tests_Common

open AST
open Value
open Bound

let u_int = Undef Type.Int
let u_bool = Undef Type.Bool
let u_bnd dims = Undef (Type.Bound dims)
let u_arr_int dims = Undef (Type.Array (Type.Int, dims))
let e_int = Error ("(ERROR constant)", false, Type.Int)
let e_float = Error ("(ERROR constant)", false, Type.Float)
let e_bool = Error ("(ERROR constant)", false, Type.Bool)
let e_bnd dims = Error ("(ERROR constant)", false, Type.Bound dims)
let e_arr_int dims = Error ("(ERROR constant)", false, Type.Array (Type.Int, dims))

[<Fact>]
let ``Scalars`` () =
    check_expr "-?" u_int
    check_expr "-ERROR" e_int

    check_expr "23 + ?" u_int
    check_expr "? + ?" u_int

    check_expr "23 + ERROR" e_int
    check_expr "23.0 + ERROR float" e_float
    check_expr "ERROR + 23" e_int
    check_expr "? + ERROR" e_int
    check_expr "ERROR + ?" e_int
    
    check_expr "if(true, 19, ERROR)" 19
    check_expr "if(true, 19, ?)" 19
    check_expr "if(false, ERROR, 19)" 19
    check_expr "if(false, ?, 19)" 19

    check_expr "if(? bool, 19, 19)" u_int
    check_expr "if(? bool, ERROR, 19)" u_int
    check_expr "if(? bool, 19, ERROR)" u_int

    check_expr "if(ERROR bool, 19, 19)" e_int
    check_expr "if(ERROR bool, ?, 19)" e_int
    check_expr "if(ERROR bool, 19, ?)" e_int

    check_expr "isDef(78)" true
    check_expr "isDef(79.3)" true
    check_expr "isDef(false)" true
    check_expr "isDef(? float)" false
    check_expr "isDef(ERROR)" e_bool
    check_expr "(forall i -> if(isDef(i),123,456))[27]" (Int 123)
    check_expr "isDense(? Bound int)" u_bool
    check_expr "isDense(ERROR Bound int)" e_bool

[<Fact>]
let ``Bounds`` () =
    check_expr "?..18" (u_bnd 1)
    check_expr "17..?" (u_bnd 1)
    check_expr "ERROR..18" (e_bnd 1)
    check_expr "17..ERROR" (e_bnd 1)
    check_expr "?..ERROR" (e_bnd 1)

    check_expr "(1..2,3..4, ? Bound int, 7..8)" (u_bnd 4)
    check_expr "(1..2,3..4, ? Bound int, ERROR Bound int)" (e_bnd 4)
    check_expr "(1..2,3..4, ERROR Bound int, ? Bound int)" (e_bnd 4)
    check_expr "(1..2,3..4,5..?,7..8)" (u_bnd 4)

[<Fact>]
let ``Arrays`` () =
    // evaluates and checks tabulate(expr)
    let check_tabbed expr exp =
        let result =
            match (eval_expr "" expr).Tabulate with
            | Error (_,dem,t) -> Error ("",dem,t)
            | other -> other
        Assert.Equal(T_to_Value exp, result)

    // evaluates and checks both expr and tabulate(expr)
    let check_ut_t expr exp_untabbed exp_tabbed =
        check_expr expr exp_untabbed
        check_tabbed expr exp_tabbed

    // dense arrays with ? and/or ERROR in their bound specifications
    check_ut_t "[ ?.. : 1,2,3,4 ]" (u_arr_int 1) (u_arr_int 1)
    check_ut_t "[ ..? : 1,2,3,4 ]" (u_arr_int 1) (u_arr_int 1)
    check_ut_t "[ ERROR.. : 1,2,3,4 ]" (e_arr_int 1) (e_arr_int 1)
    // even though ERROR occurs as an element, tabulation gives ? instead of ERROR since the bound
    // cannot be evaluated (it evaluates to ?)
    check_ut_t "[ ?.. : 1,ERROR,3,4 ]" (u_arr_int 1) (u_arr_int 1)

    // dense arrays with ? and/or ERROR as elements
    do  let elems = Array.map Int [|1..8|]
        elems[3] <- u_int
        let arr =  Abst_Array (Type.Int, Bound (10,17), elems)
        check_ut_t "[ 10.. : 1,2,3,?,5,6,7,8 ]" arr arr
        elems[4] <- e_int
        let arr = Abst_Array (Type.Int, Bound (10,17), elems)
        check_ut_t "[ 10.. : 1,2,3,?,ERROR,6,7,8 ]" arr (e_arr_int 1)
        elems[3] <- e_int
        let arr = Abst_Array (Type.Int, Bound (10,17), elems)
        check_ut_t "[ 10.. : 1,2,3,ERROR,ERROR,6,7,8 ]" arr (e_arr_int 1)
        elems[4] <- u_int
        let arr = Abst_Array (Type.Int, Bound (10,17), elems)
        check_ut_t "[ 10.. : 1,2,3,ERROR,?,6,7,8 ]" arr (e_arr_int 1)

    // sparse arrays with ? and/or ERROR as indices
    check_ut_t "[ ?:1, 2:2, 3:3, 4:4 ]" (u_arr_int 1) (u_arr_int 1)
    check_ut_t "[ 1:1, 2:2, 3:3, ?:4 ]" (u_arr_int 1) (u_arr_int 1)
    check_ut_t "[ ?:1, ERROR:2, 3:3, 4:4 ]" (e_arr_int 1) (e_arr_int 1)

    // sparse arrays with ? and/or ERROR as elements
    do  let arr = Abst_Array (Type.Int, [(Index [1], u_int); (Index [2], Int 2); (Index [3], Int 3); (Index [4], Int 4)])
        check_ut_t "[ 1:?, 2:2, 3:3, 4:4 ]" arr arr
    do  let arr = Abst_Array (Type.Int, [(Index [1], Int 1); (Index [2], Int 2); (Index [3], Int 3); (Index [4], u_int)])
        check_ut_t "[ 1:1, 2:2, 3:3, 4:? ]" arr arr
    check_tabbed "[ 1:?, 2:ERROR, 3:3, 4:4 ]" (e_arr_int 1)
    check_tabbed "[ 1:ERROR, 2:2, 3:3, 4:4 ]" (e_arr_int 1)
    check_tabbed "[ ?:ERROR, 2:2, 3:3, 4:4 ]" (u_arr_int 1)

    // some multidimensional examples
    check_ut_t "[ (?..,10..) : 1,2,3,4; 5,6,7,8 ]" (u_arr_int 2) (u_arr_int 2)
    check_ut_t "[ (0..,10..,..?) : 1,2; 3,4;; 5,6; 7,8 ]" (u_arr_int 3) (u_arr_int 3)
    check_tabbed "[ (0..,10..,..102) : 1,2; 3,4;; 5,6; ERROR,8 ]" (e_arr_int 3)

    // array comprehensions
    do  let arr = Abst_Array (Type.Int, Bound (-1,2), [|u_int;Int 13;Int 72;u_int|])
        // TODO: check "[ [13,72][i] : i in -1..2 ]" arr
        check_ut_t "[ [ -1.. : ?,13,72,? ][i] : i in -1..2 ]" arr arr
    // TODO: correct?
    do  let arr = Abst_Array (Type.Int, Bound (10,20), Array.replicate 11 e_int)
        check_expr "[ ERROR : i in 10..20 ]" arr

    // the bound() function
    check_expr "bound([ ?.. : 17 ])" (u_bnd 1)
    check_expr "bound([ ?.. : ERROR ])" (u_bnd 1)

