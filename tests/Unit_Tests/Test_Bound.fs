module Test_Bound

open Xunit
open Tests_Common

open Bound

[<Fact>]
let ``"all" and "empty"`` () =
    Assert.True(not (Empty.Contains (Index [1;2;3])))
    Assert.Equal(0, Empty.Size)
    Assert.True(not (Empty_3.Contains (Index [1;2;3])))
    Assert.Equal(0, Empty_3.Size)
    Assert.True(not (Empty_2.Contains (Index [1;2])))
    Assert.Equal(0, Empty_2.Size)
    Assert.True(not (Empty_2.Contains (Index [1;2])))
    Assert.Equal(0, Empty_2.Size)
    Assert.True(All.Contains (Index [72]))
    Assert.True(All.Contains (Index [72;19]))
    Assert.Equal(-1, All.Size)
    let All_5 = Bound (5,true)
    Assert.True(All_5.Contains (Index [1;2;3;4;5]))
    Assert.Equal(-1, All_5.Size)

[<Fact>]
let ``Dense bounds`` () =
    let dense_3 = Bound [(1,1);(5,7);(100,110)]
    Assert.True(dense_3.Contains (Index [1;5;101]))
    Assert.Equal(1*3*11, dense_3.Size)

[<Fact>]
let ``Approximating sparse bounds as products`` () =
    let sparse_to_product =
        function
        | Sparse (d,elems,emb) -> sparse_to_product d elems emb
        | _ -> failwith ""

    // 3D bound embedded in 7 dimensions
    do  let result = sparse_to_product (Bound (7, gen_indices_3 (1,4) (1,2) (5,7), [1;2;5]))
        let exp =
            Bound [
                All_1;
                Bound [1..4];
                Bound [1..2];
                All_1;
                All_1;
                Bound [5..7];
                All_1
            ]
        Assert.Equal(exp, result)
    // same as previous but the first dimension has been removed
    do  let result = sparse_to_product (Bound (6, gen_indices_3 (1,4) (1,2) (5,7), [0;1;4]))
        let exp =
            Bound [
                Bound [1..4];
                Bound [1..2];
                All_1;
                All_1;
                Bound [5..7];
                All_1
            ]
        Assert.Equal(exp, result)
    // same again except the last dimension has been removed
    do  let result = sparse_to_product (Bound (6, gen_indices_3 (1,4) (1,2) (5,7), [1;2;5]))
        let exp =
            Bound [
                All_1;
                Bound [1..4];
                Bound [1..2];
                All_1;
                All_1;
                Bound [5..7];
            ]
        Assert.Equal(exp, result)

[<Fact>]
let ``Predicate bounds`` () =
    let check = check_expr_ctx "
        bnd : Bound (int,int)
        bnd = { (i,j) : 10 * i < j }
    "
    check "isDense(bnd)" false
    check "isSparse(bnd)"  false
    check "isPredicate(bnd)" true
    check "isProduct(bnd)" false
    check "finite(bnd)" false
    check "member((3,38), bnd)" true
    check "member((5,50), bnd)" false
    check "member((6,65), bnd)" true

[<Fact>]
let ``Product bounds`` () =
    let check = check_expr_ctx "
        dense, sparse : Bound int
        prod : Bound (int,int)

        dense = 10..19
        sparse = { 2,7,9 }
        prod = (dense,sparse)
    "
    check "isDense(prod)" false
    check "isSparse(prod)" false
    check "isPredicate(prod)" false
    check "isProduct(prod)" true
    check "finite(prod)" true
    check "member((12,7), prod)" true
    check "member((12,9), prod)" true
    check "member((10,8), prod)" false
    check "member(( 9,2), prod)" false
    check "member((9,10), prod)" false

[<Fact>]
let ``Enumeration`` () =
    let dense_3 = eval_expr_Bound "" "(0..4, 10..14, 100..101)"
    Assert.Equal<Index seq> (dense_3.Get_Seq, gen_indices_3 (0,4) (10,14) (100,101))

    let prod_3 = eval_expr_Bound "" "(1..2, { 7,19 }, 100..102)"
    Assert.Equal<Index seq> (prod_3.Get_Seq,
        List.map Index [
            [1; 7;100];
            [1; 7;101];
            [1; 7;102];
            [1;19;100];
            [1;19;101];
            [1;19;102];
            [2; 7;100];
            [2; 7;101];
            [2; 7;102];
            [2;19;100];
            [2;19;101];
            [2;19;102]])

[<Fact>]
let ``join()`` () =
    let check expr exp_value =
        check_expr_ctx "
            dense1 : Bound int
            sparse2 : Bound (int,int)

            dense1 = join(0..9, 20..29)
            sparse2 = join({(1,1),(2,2)}, {(1,1),(3,3),(2,3)})
        " expr exp_value

    check "size(dense1) = 30" true
    check "member(0, dense1)" true
    check "member(10, dense1)" true
    check "member(15, dense1)" true
    check "member(29, dense1)" true
    check "member(30, dense1)" false

    check "size(sparse2) = 4" true
    check "member((1,1), sparse2)" true
    check "member((2,2), sparse2)" true
    check "member((3,3), sparse2)" true
    check "member((2,3), sparse2)" true
    check "member((3,2), sparse2)" false

    //check "join(0..9, { 5,9,11 })" (Bound (0,11))
    check "join(0..9, { 5,9,11 })" (Bound [0;1;2;3;4;5;6;7;8;9;11])

    //// join(5..9 × 50..57, { (0,51),(2,59),(8,52) }) = 0..9 × 50..59
    //Assert.Equal(Bound [(0,9);(50,59)],
    //    join (Bound [(5,9);(50,57)])
    //         (eval_expr_Bound "" "{ (0,51),(2,59),(8,52) }"))

[<Fact>]
let ``join() with "all" and "empty"`` () =
    let dense2 = Bound [(5,9);(20,27)]

    Assert.Equal(Empty, join Empty Empty)
    Assert.Equal(All, join All All)
    Assert.Equal(All, join All Empty)
    Assert.Equal(All, join Empty All)

    Assert.Equal(Empty_2, join Empty_2 Empty)
    Assert.Equal(Empty_2, join Empty Empty_2)
    Assert.Equal(All_2, join All Empty_2)
    Assert.Equal(All_2, join Empty_2 All)

    Assert.Equal(All_2, join All_2 All)
    Assert.Equal(All_2, join All All_2)
    Assert.Equal(All_2, join All_2 Empty)
    Assert.Equal(All_2, join Empty All_2)

    Assert.Equal(Empty_2, join Empty_2 Empty_2)
    Assert.Equal(All_2, join All_2 All_2)
    Assert.Equal(All_2, join All_2 Empty_2)
    Assert.Equal(All_2, join Empty_2 All_2)

    Assert.Equal(All_2, join All dense2)
    Assert.Equal(All_2, join dense2 All)
    Assert.Equal(dense2, join Empty dense2)
    Assert.Equal(dense2, join dense2 Empty)

[<Fact>]
let ``join() with sparse bounds embedded in higher dimensions`` () =
    // { (x_0,...,x_5) : x_3 = 1, x_0 ∈ {2,7,9}, x_5 = 3 } ⊔
    // { (x_0,...,x_5) : x_0 = 1, x_5 = {2,19}, x_4 = 3, x_2 = 2 }
    // =
    // { (x_0,...,x_5) : (x_0,x_5) ∈ { (2,3),(7,3),(9,3),(1,2),(1,19) } }
    let bnd1 = Bound (6, List.map Index [[1;2;3];[1;7;3];[1;9;3]], [3;0;5])
    let bnd2 = Bound (6, List.map Index [[1;2;3;4];[1;19;3;4]], [0;5;4;2])
    let exp  = Bound (6, List.map Index [[2;3];[7;3];[9;3];[1;2];[1;19]], [0;5])
    Assert.Equal(exp, join bnd1 bnd2)

    let bnd1 = Bound (3, List.map Index [[1;2;3];[2;3;4]])
    let bnd2 = Bound (3, List.map Index [[4;5];[5;6]], [1;2])
    let exp  = Bound (3, List.map Index [[2;3];[3;4];[4;5];[5;6]], [1;2])
    Assert.Equal(exp, join bnd1 bnd2)

[<Fact>]
let ``meet()`` () =
    let check = check_expr_ctx "
        dense1 : Bound int
        sparse3 : Bound (int,int,int)
        e1 : Bound int

        dense1 = meet(0..9, 5..14)
        sparse3 = meet({(1,1,1),(2,2,2)}, {(1,2,3),(2,2,2),(3,2,1)})
    "
    check "size(meet(empty, 10..19)) = 0" true
    check "size(meet(empty, all)) = 0" true
    check "size(meet(all, empty)) = 0" true
    check "size(meet(dense1, all)) = 5" true
    check "size(meet(sparse3, all)) = 1" true

    check "size(dense1) = 5" true
    check "member(0, dense1)" false
    check "member(5, dense1)" true
    check "member(9, dense1)" true
    check "member(10, dense1)" false
    check "member(14, dense1)" false

    check "size(sparse3) = 1" true
    check "member((1,1,1), sparse3)" false
    check "member((2,2,2), sparse3)" true

    let dense2 = Bound [(5,9);(20,27)]

    Assert.Equal(Empty, meet Empty Empty)
    Assert.Equal(All, meet All All)
    Assert.Equal(Empty, meet All Empty)
    Assert.Equal(Empty, meet Empty All)

    Assert.Equal(Empty_2, meet Empty_2 Empty)
    Assert.Equal(Empty_2, meet Empty Empty_2)
    Assert.Equal(Empty_2, meet All Empty_2)
    Assert.Equal(Empty_2, meet Empty_2 All)

    Assert.Equal(All_2, meet All_2 All)
    Assert.Equal(All_2, meet All All_2)
    Assert.Equal(Empty_2, meet All_2 Empty)
    Assert.Equal(Empty_2, meet Empty All_2)

    Assert.Equal(Empty_2, meet Empty_2 Empty_2)
    Assert.Equal(All_2, meet All_2 All_2)
    Assert.Equal(Empty_2, meet All_2 Empty_2)
    Assert.Equal(Empty_2, meet Empty_2 All_2)

    Assert.Equal(dense2, meet All dense2)
    Assert.Equal(dense2, meet dense2 All)
    Assert.Equal(Empty_2, meet Empty dense2)
    Assert.Equal(Empty_2, meet dense2 Empty)

[<Fact>]
let ``meet() with sparse bounds embedded in higher dimensions`` () =
    // { (x,y) : x ∈ [1..5] } ⊓ { (x,y) : y ∈ [10..14] }
    // =
    // { (x,y) : x ∈ [1..5], y ∈ [10..14] }
    let bnd1 = Bound (2, gen_indices_1 (1,5), [0])
    let bnd2 = Bound (2, gen_indices_1 (10,14), [1])
    let exp  = Bound (2, gen_indices_2 (1,5) (10,14))
    Assert.Equal(exp, meet bnd1 bnd2)

    // { (x,y,z) : x ∈ [1..5], y ∈ [1..2] } ⊓ { (x,y,z) : x ∈ [1..4], z ∈ [5..7] }
    // =
    // { (x,y,z) : x ∈ [1..4], y ∈ [1..2], z ∈ [5..7] }
    let bnd1 = Bound (3, gen_indices_2 (1,5) (1,2), [0;1])
    let bnd2 = Bound (3, gen_indices_2 (1,4) (5,7), [0;2])
    let exp  = Bound (3, gen_indices_3 (1,4) (1,2) (5,7))
    Assert.Equal(exp, meet bnd1 bnd2)
