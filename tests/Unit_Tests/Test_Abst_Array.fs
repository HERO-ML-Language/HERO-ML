module Test_Abst_Array

open Xunit
open Tests_Common

open AST
open Value
open Bound

let test_populate (generator : Index -> Value) (to_populate : Abst_Array) (indices : Index seq)  =
    let num_indices = Seq.length indices
    Assert.Equal(num_indices, to_populate.Size)
    // write values to array
    let populated =
        (to_populate, indices)
        ||> Seq.fold (fun arr idx -> arr.Update idx (generator idx))
    Assert.Equal(num_indices, populated.Size)
    // read off the values and compare to what was written
    Assert.True(Seq.forall (fun idx -> populated.Access idx = generator idx) indices)

[<Fact>]
let ``Populate one-dimensional arrays`` () =
    let idx_range = (1,9)
    let indices = gen_indices_1 idx_range
    let generator (idx : Index) = Int idx.Head
    let dense = Abst_Array (Type.Int, Bound idx_range)
    let sparse = Abst_Array (Type.Int, Bound indices)
    test_populate generator dense indices
    test_populate generator sparse indices
    
[<Fact>]
let ``Populate two-dimensional arrays`` () =
    let idx_ranges = [(100,109);(0,4)]
    let indices = gen_indices_2 idx_ranges[0] idx_ranges[1]
    let generator (idx : Index) = Float (float (10 * idx[0] + idx[1]))
    let dense = Abst_Array (Type.Float, Bound idx_ranges)
    let sparse = Abst_Array (Type.Float, Bound indices)
    test_populate generator dense indices
    test_populate generator sparse indices

[<Fact>]
let ``Empty arrays`` () =
    let error = Error ("Array access out-of-bounds", true, Type.Int)
    do  let arr = Abst_Array (Type.Int, Empty_3)
        Assert.Equal(0, arr.Size)
        Assert.Equal(error, arr.Access (Index [27;13;92]))
    do  let arr = Abst_Array (Type.Int, Bound (7,[]))
        Assert.Equal(0, arr.Size)
        Assert.Equal(error, arr.Access (Index [5..11]))
    do  let arr = Abst_Array (Type.Int, Bound [(1,0);(100,199)])
        Assert.Equal(0, arr.Size)
        Assert.Equal(error, arr.Access (Index [27;13]))
    do  let arr = Abst_Array (Type.Int, Bound [(100,199);(1,0)])
        Assert.Equal(0, arr.Size)
        Assert.Equal(error, arr.Access (Index [27;13]))

[<Fact>]
let ``Dense arrays`` () =
    let undef = Undef (Type.Array (Type.Int, 1))
    let error = Error ("", false, Type.Array (Type.Int, 1))

    check_expr "[ 1..  : 1,2,3 ]" (array_dense [(1,3)] [|1;2;3|])
    check_expr "[ ..3  : 1,2,3 ]" (array_dense [(1,3)] [|1;2;3|])
    check_expr "[ 1..3 : 1,2,3 ]" (array_dense [(1,3)] [|1;2;3|])

    check_expr "[ 1..2 : 1,2,3 ]" error // bound doesn't match the number of elements
    check_expr "[ 1..4 : 1,2,3 ]" error // -"-
    check_expr "[ 3..1 : 1,2,3 ]" error // inverted bound

    check_expr "[ ?..  : 1,2,3 ]" undef
    check_expr "[ ..?  : 1,2,3 ]" undef
    check_expr "[ 1..? : 1,2,3 ]" undef
    check_expr "[ ?..3 : 1,2,3 ]" undef
    check_expr "[ ?..? : 1,2,3 ]" undef

    check_expr "[ ERROR..  : 1,2,3 ]" error
    check_expr "[ ..ERROR  : 1,2,3 ]" error
    check_expr "[ 1..ERROR : 1,2,3 ]" error
    check_expr "[ ERROR..3 : 1,2,3 ]" error

    check_expr "[ ERROR..? : 1,2,3 ]" error
    check_expr "[ ?..ERROR : 1,2,3 ]" error

[<Fact>]
let ``Sparse arrays`` () =
    let ``?`` = System.Int32.MinValue
    do  let bnd = Bound (1,10)
        let elems = [ (1,2);(3,6);(4,8);(7,14) ] |> List.map (fun (idx,value) -> (Index [idx], Int value))
        let arr = Abst_Array (Type.Int, bnd, elems)
        let exp_seq =
            [ 2;``?``;6;8;``?``;``?``;14;``?``;``?``;``?`` ]
            |> List.mapi (fun i v -> (Index [i+1], if v = ``?`` then Undef Type.Int else Int v))
        Assert.Equal<(Index * Value) seq> (exp_seq, arr.Get_Seq)

[<Fact>]
let ``Array comprehensions`` () =
    let check expr exp_value =
        check_expr_ctx "
            A,C : Array int int
            B : Array (int,int) int

            A = [ i - 17 : i in 17..23 ]
            B = [ 10*i + j : (i,j) in (0..5,0..9) ]
            // TODO: C = [ A[i] : i in 20..26 ]
        " expr exp_value
    let undef = Undef Type.Int
    let error = Error ("", true, Type.Int)

    check "A[16]" error
    check "A[17]" 0
    check "A[18]" 1
    check "A[23]" 6
    check "A[24]" error

    check "B[0,0]" 0
    check "B[1,0]" 10
    check "B[5,9]" 59
    check "B[6,0]" error

    // TODO:
    //check "C[17]" error
    //check "C[19]" error
    //check "C[20]" 3
    //check "C[23]" 6
    //check "C[24]" undef // out-of-bounds of A but not of C
    //check "C[26]" undef // -"-
    //check "C[27]" error

    // here the array is inlined because infinite arrays cannot be stored in variables
    let check_pred expr exp_val =
        check_expr (sprintf expr "[ 10*i + j : (i,j) : i != j ]") exp_val

    check_pred "%s[1,3]" 13
    check_pred "%s[2,3]" 23
    check_pred "%s[3,3]" error
    check_pred "%s[4,3]" 43

[<Fact>]
let ``Array slicing`` () =
    check_expr "[ 2*i : i : i > 0 ] | -10..10" (array_sparse_1d (seq { for i in 1..10 -> (i,2*i) }))

[<Fact>]
let ``reduce()`` () =
    let check expr exp_value =
        check_expr_ctx "
            A : Array int int
            B : Array (int,int) int

            // [ 20,21,...,29 ]
            A = [ i : i in 20..29 ]

            // [ (1,3):13, (1,4):14, ..., (1,7):17
            //   (2,3):23, (2,4):24, ..., (2,7):27
            //   (3,3):33, (3,4):34, ..., (3,7):37 ]
            B = [ 10*i+j : (i,j) in ({ 1,2,3 }, 3..7) ]
        " expr exp_value

    check "reduce(*, [ 123 : i in empty ])" (Error ("", false, Type.Int))

    do  let exp = List.sum [20..29]
        check "reduce(+,A)" exp
        check "reduce(+, [ 49 - i : i in bound(A) ])" exp // A backwards
        // TODO: check "reduce(+, [ A[i] : i in 15..34 ])" exp // this should skip over values of i ∈ { 15,...,19 } ∪ { 30,...,34 }
        check "reduce(+, [ 2 * A[i] + 1 : i in { 20,22,24,26,28 } ])" exp // sparse array
        // [ 2 * A[j] + 1 : j = i for even i ∈ bound(A), j = -i for odd i ∈ bound(A) ]
        //     = [ 2*A[20]+1, ?, 2*A[22]+1, ?, ..., 2*A[28]+1, ? ]
        // TODO: check "reduce(+, [ 2 * A[(2*(i/2*2-i)+1) * i] + 1 : i in bound(A) ])" exp
        check "reduce(+, [ A[j] : (i,j,k) in ({41}, bound(A), 923..923) ])" exp
        check "reduce(+, [ A[j] : (i,j,k) in ({41}, bound(A), 923..924) ])" (2*exp)

    do  let exp = 5 * (10+20+30) + 3 * (List.sum [3..7])
        check "reduce(+,B)" exp
        check "reduce(+, [ reduce(+, [ B[i,j] : j in 3..7 ]) : i in 1..3 ])" exp

    check "reduce(-,A)" (List.reduce (-) [20..29])

    check "reduce(&&, [ i-i/2*2 = 0 : i in 0..5 ])" false
    check "reduce(&&, [ i-i/2*2 = 0 : i in { 0,2,4 } ])" true
    check "reduce(||, [ i-i/2*2 = 0 : i in 0..5 ])" true
    check "reduce(||, [ i-i/2*2 = 0 : i in { 0,2,4 } ])" true
    check "reduce(||, [ i-i/2*2 = 0 : i in { 1,3,5 } ])" false

    check "reduce(+, [ 1,2,ERROR,3 ])" (Error ("", false, Type.Int))

    check "reduce(meet, [1..4, 2..5, 3..6, 4..7])" (Bound (4,4))
    check "reduce(join, [1..4, 2..5, 3..6, 4..7])" (Bound (1,7))

[<Fact>]
let ``scan()`` () =
    let check expr exp_value =
        check_expr_ctx "
            A : Array int int
            B : Array (int,int) int

            // [ -10,-9,...,9,10 ]
            A = [ i : i in -10..10 ]

            // [                           (-1,0):-10
            //   (0,-9):-9, (0,-8):-8, ..., (0,0):0, ..., (0,8):8, (0,9):9
            //                              (1,0):10                       ]
            B = [ 10*i+j : (i,j) in join(({0},-9..9), {(-1,0),(1,0)}) ]
        " expr exp_value

    let exp_vals = [|-10..10|] |> Array.scan (+) 0 |> Array.tail |> Array.map Int
    do  let exp_arr = array_dense [(-10,10)] exp_vals
        check "scan(+,A)" exp_arr
    // TODO:
    //do  let undefs = Array.create 5 (Undef Type.Int)
    //    let exp_arr = array_dense [(-15,15)] (Array.concat [undefs; exp_vals; undefs])
    //    check "scan(+, [ A[i] : i in -15..15 ])" exp_arr
    do  let exp_idcs = [-10..10] |> List.map (fun i -> [i/10; i%10])
        let exp_arr = array_sparse (Seq.zip exp_idcs exp_vals)
        check "scan(+,B)" exp_arr

[<Fact>]
let ``Pretty printing`` () =
    // dense 1D arrays
    do  let A = eval_expr_Array "" "[ 1,3,6,8 ]"
        Assert.Equal("[ 1, 3, 6, 8 ]", A.Str)
        Assert.Equal("[ 1, 3, 6, ... ]", A.Str_Trunc 3)
        Assert.Equal("[ 1, 3, ... ]", A.Str_Trunc 2)
    do  let A = eval_expr_Array "" "[ 0.. : 1,3,6,8 ]"
        Assert.Equal("[ 1, 3, 6, 8 ]", A.Str)
        Assert.Equal("[ 1, 3, 6, ... ]", A.Str_Trunc 3)
        Assert.Equal("[ 1, 3, ... ]", A.Str_Trunc 2)
    do  let A = eval_expr_Array "" "[ -7.. : 1,3,6,8 ]"
        Assert.Equal("[ -7..-4 : 1, 3, 6, 8 ]", A.Str)
        Assert.Equal("[ -7..-4 : 1, 3, 6, ... ]", A.Str_Trunc 3)
        Assert.Equal("[ -7..-4 : 1, 3, ... ]", A.Str_Trunc 2)

    // sparse 1D arrays
    do  let A = eval_expr_Array "" "[ 0:1,1:3,2:6,3:8 ]"
        Assert.Equal("[ 0:1, 3, 6, 8 ]", A.Str)
        Assert.Equal("[ 0:1, 3, 6, ... ]", A.Str_Trunc 3)
        Assert.Equal("[ 0:1, 3, ... ]", A.Str_Trunc 2)
    do  let A = eval_expr_Array "" "[ 3:1,4:3,5:6,9:8 ]"
        Assert.Equal("[ 3:1, 3, 6, 9:8 ]", A.Str)
        Assert.Equal("[ 3:1, 3, 6, ... ]", A.Str_Trunc 3)
        Assert.Equal("[ 3:1, 3, ... ]", A.Str_Trunc 2)

    // dense 2D arrays
    do  let A = eval_expr_Array "" "[ 4*i+j : (i,j) in (0..2,0..3) ]"
        Assert.Equal("[ 0, 1,  2,  3\n" +
                     "  4, 5,  6,  7\n" +
                     "  8, 9, 10, 11 ]", A.Str)
        Assert.Equal("[ 0, 1,  2,   3\n" +
                     "  4, 5,  6,   7\n" +
                     "  8, 9, 10, ... ]", A.Str_Trunc 11)
        Assert.Equal("[ 0,   1, 2, 3\n" +
                     "  4,   5, 6, 7\n" +
                     "  8, ...       ]", A.Str_Trunc 9)
        Assert.Equal("[ 0, 1, 2, ... ]", A.Str_Trunc 3)
    do  let A = eval_expr_Array "" "[ 4*(i-1)+(j-10) : (i,j) in (1..3,10..13) ]"
        Assert.Equal("[ (1..3, 10..13) :\n" +
                     "  0, 1,  2,  3\n" +
                     "  4, 5,  6,  7\n" +
                     "  8, 9, 10, 11 ]", A.Str)
        Assert.Equal("[ (1..3, 10..13) :\n" +
                     "  0, 1,  2,   3\n" +
                     "  4, 5,  6,   7\n" +
                     "  8, 9, 10, ... ]", A.Str_Trunc 11)
        Assert.Equal("[ (1..3, 10..13) :\n" +
                     "  0,   1, 2, 3\n" +
                     "  4, ...       ]", A.Str_Trunc 5)
        Assert.Equal("[ (1..3, 10..13) :\n" +
                     "  0, 1, 2, ... ]", A.Str_Trunc 3)

    // sparse 2D arrays
    do  let A = eval_expr_Array "" "[ 4*i+j : (i,j) in { (0,0),(0,1),(0,3),(2,0),(2,2) } ]"
        Assert.Equal("[ (0,0):0, 1, (0,3):3\n" +
                     "  (2,0):8, (2,2):10 ]", A.Str)

    // dense 3D arrays
    do  let A = eval_expr_Array "" "[ 12*(i-2)+3*(j-10)+(k-5) : (i,j,k) in (2..3,10..13,5..7) ]"
        Assert.Equal("[ (2..3, 10..13, 5..7) :\n" +
                     "   0,  1,  2\n" +
                     "   3,  4,  5\n" +
                     "   6,  7,  8\n" +
                     "   9, 10, 11\n" +
                     "\n" +
                     "  12, 13, 14\n" +
                     "  15, 16, 17\n" +
                     "  18, 19, 20\n" +
                     "  21, 22, 23 ]", A.Str)
        Assert.Equal("[ (2..3, 10..13, 5..7) :\n" +
                     "  0,  1,   2\n" +
                     "  3,  4,   5\n" +
                     "  6,  7,   8\n" +
                     "  9, 10, ... ]", A.Str_Trunc 11)
        Assert.Equal("[ (2..3, 10..13, 5..7) :\n" +
                     "    0,  1,  2\n" +
                     "    3,  4,  5\n" +
                     "    6,  7,  8\n" +
                     "    9, 10, 11\n" +
                     "\n" +
                     "  ...         ]", A.Str_Trunc 12)

    // sparse 3D arrays
    do  let A = eval_expr_Array "" "[ 12*(i-2)+3*(j-10)+(k-5) : (i,j,k) in\
                                           { (2,11,6),(2,11,7),(2,13,5),(2,13,7),(3,13,5),(3,13,6),(3,13,7) } ]"
        Assert.Equal("[ (2,11,6):4, 5\n" +
                     "  (2,13,5):9, (2,13,7):11\n" +
                     "\n" +
                     "  (3,13,5):21, 22, 23 ]", A.Str)
