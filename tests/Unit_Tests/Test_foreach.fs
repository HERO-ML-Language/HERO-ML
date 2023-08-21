module Test_foreach

open Xunit
open Tests_Common

[<Fact>]
let ``foreach with dense bounds`` () =
    let check stmt expr =
        check_expr_ctx (
            sprintf "
                A : Array int int
                A = [ i : i in 1..10 ]
                %s" stmt) expr

    do  let exp = array_dense [(1,10)] [|1;2;3;-4;-4;-4;7;8;9;10|]
        check "foreach i in 5..7 do A[i-1] = -A[4]" "A" exp

    do  let exp = array_dense [(1,10)] [|1;-1;-2;-3;-4;-5;-6;-7;-8;-9|]
        check "foreach i do A[i] = -A[i-1]" "A" exp
        check "foreach i do A[i] = -A[A[i-1]]" "A" exp

    // syntactic sugar for
    // foreach i in { i : i <= 5 } do A[i] = 2 * A[i]
    do  let exp = array_dense [(1,10)] [|2;4;6;8;10;6;7;8;9;10|]
        check "foreach i : i <= 5 do A[i] = 2 * A[i]" "A" exp
        check "foreach i : i <= 5 do A[i] = 2 * i" "A" exp

    do  let exp = array_dense [(1,10)] [|1;2;3;4;5;3;6;9;12;15;|]
        check "foreach i do A[i+5] = 3 * A[i]" "A" exp

    // syntactic sugar for
    // foreach i in all do A[i] = -A[i]
    do  let exp = array_dense [(1,10)] (Array.rev [|-10..-1|])
        check "foreach i do A[i] = -A[i]" "A" exp
