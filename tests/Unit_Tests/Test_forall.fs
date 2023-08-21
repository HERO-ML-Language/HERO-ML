module Test_forall

open Xunit
open Tests_Common

open AST
open Value
open Bound

let undef dims = Undef (Type.Bound dims)
let error dims = Error ("", true, Type.Bound dims)

[<Fact>]
let ``forall with empty bounds and "all"`` () =
    check_expr "bound(forall i -> [ i : i in empty ][i])" Empty_1
    check_expr "bound(forall i -> [ i : i in empty ][i] + [ i : i in 1..10 ][i])" Empty_1
    check_expr "bound(forall (i,j) -> [ i + j : (i,j) in (1..10,empty) ][i,j])" Empty_2 // the array's bound becomes "empty"
    check_expr "bound(forall (i,j) -> [ i : i in empty ][i])" Empty_2 // since i is constrained to "empty", the overall result is "empty"

    check_expr "bound(forall i -> [ i : i in all ][i])" All_1
    check_expr "bound(forall i -> [ i : i in all ][i] + [ i : i in 1..10 ][i])" (Bound (1,10))
    check_expr "bound(forall (i,j) -> [ i + j : (i,j) in (all,all) ][i,j])" (Bound [All_1;All_1])
    check_expr "bound(forall (i,j) -> [ i + j : (i,j) in (all,all) ][i,j] + [ i : i in 1..10 ][j])" (Bound ([All_1; Bound (1,10)]))

[<Fact>]
let ``forall with dense bounds`` () =
    let check expr exp_val =
        check_expr_ctx "
            A, B : Array int int
            C : Array (int,int) int
            n : int

            A = [ 1,3,65,432,432,7,3 ]
            B = [ 10.. : 4,23,9 ]
            C = [ 1000 * i + j : (i,j) in (10..19,200..219) ]
            n = 10
        " expr exp_val
    let bound_A = Bound (0,6)
    let bound_B = Bound (10,12)

    check "bound(A)" bound_A
    check "bound(B)" bound_B
    check "meet(bound(A),bound(B))" Empty_1

    check "bound(forall i -> A[i])" bound_A
    check "bound(forall n -> A[n])" bound_A
    check "bound(forall i -> (forall j -> A[j] + i)[i])" bound_A
    check "bound(forall i -> (forall j -> A[j] + B[i])[i])" Empty_1
    check "bound(forall i -> [ ..n : 4,5,6,B[i] ][i])" (Bound (7,10)) // B[i] is not necessarily evaluated
    check "bound(forall i -> [ A[i].. : 4,5,6 ][i])" bound_A
    check "bound(forall i -> A[5])" All_1       // doesn't constrain i
    check "bound(forall i -> A[50])"  (error 1) // A[50] is independent of i and evaluates to ERROR
    check "bound(forall i -> ? bool)" (undef 1)                     // the body is independent of i and evaluates to "?"
    check "forall i -> ? float" (Undef (Type.Array (Type.Float,1))) // -"-
    check "bound(forall i -> if(true,  ?, 17))" (undef 1)     // -"-
    check "bound(forall i -> if(false, ?, 17))" All_1 // doesn't constrain i

    check "bound(forall i -> if(n < 20, A[i], B[i]))" bound_A
    check "bound(forall i -> if(n > 20, A[i], B[i]))" bound_B
    check "bound(forall i -> if(i < n, A[i], B[i]))" (Bound (0,12)) // = join(bound(A),bound(B))

    // The right operand of || never needs to be evaluated because n < 20 holds
    // for all i. Also, the returned bound should be
    // meet(all,join(bound(A),all)) = bound(A), since the true branch is always
    // evaluated and the false branch never.
    check "bound(forall i -> if(n < 20 || B[i] = 22, A[i], 17))" bound_A

    // Swap the operands to || and now the resulting bound is
    // meet(bound(B),join(bound(A),all)) = bound(B), even though we still know
    // that the condition will always be true for the values of i for which it
    // is defined. This is according to the semantics of forall, however.
    // TODO: check "bound(forall i -> if(B[i] = 22 || n < 20, A[i], 17))" bound_B

    // the two one-dimensional bounds of A and B should be combined into one two-dimensional bound
    check "bound(forall (i,j) -> A[i] * B[j])" (Bound [bound_A;bound_B])

    // with affine transformations of the index
    check "bound(forall i -> A[i+5])" (Bound (-5,1))
    check "bound(forall i -> A[2+i])" (Bound (-2,4))
    check "bound(forall i -> B[i-1])" (Bound (11,13))
    check "bound(forall k -> C[k - 200, k])" (Bound (210,219))
    check "bound(forall i -> A[2*i - 3*i + 7 + 2*i + (23 - 13 - 10) * (i * i) - 7])" bound_A // = bound(forall i -> A[i])
    check "bound(forall i -> A[-(i+2)])" (Bound (-8,-2))

    // with strides of magnitudes larger than 1
    check "bound(forall i -> A[2*i])"   (Bound (0,3))
    check "bound(forall i -> A[2*i+1])" (Bound (0,2))
    check "bound(forall (i,j) -> C[5*i,7*j])" (Bound [(2,3);(29,31)]) // (2..3,29..31)
    check "bound(forall i -> C[6*i,67*i])" (Bound (3,3)) // 6*3 ∈ 10..19, 67*3 ∈ 200..219

    // more thorough checking
    let check2 l u s o =
        let expr = sprintf "bound(forall i -> [ 0 : j in %d..%d ][%d*i+%d])" l u s o
        let l' = (float (l - o)) / (float s)
        let u' = (float (u - o)) / (float s)
        check_expr expr (Bound (int (ceil (min l' u')), int (floor (max l' u'))))

    //       l  u  s  o
    // ----------------
    check2   0  0  3  0
    check2   0  0 -3  0
    check2   0  5  3  0
    check2   0  5 -3  0
    check2  -5  0  3  0
    check2  -5  0 -3  0
    check2  -9 12  3  0
    check2  -9 12 -3  0
    check2  -8 13  3  0
    check2  -8 13 -3  0
    check2 -12 -9  3  0
    check2 -12 -9 -3  0
    check2 -14 -8  3  0
    check2 -14 -8 -3  0
    check2 -14 -8  3  1
    check2 -14 -8 -3  1
    check2 -14 -8  3  2
    check2 -14 -8 -3  2
    check2 -14 -8  3 -2
    check2 -14 -8 -3 -2

    // some odd corner cases ---------------------------------------------------->

    check "bound(forall i -> 27 + [ 13:0 ][i])" (Bound [13])
    check "bound(forall i -> 13 + [ 0 : j in 1..10 ][i])" (Bound (1,10))
    // even though the body evaluates to an array and not a scalar, it is still constant
    check "bound(forall i -> [ [ j+k : k in 0..2 ] : j in 1..17 ])" All_1
    // the body evaluates to the constant [ 1..2 : 7, 92 ], thus the bound is "all"
    check "bound(forall i -> ([ A[i], 7, 92, A[i] ] | 1..2))" All_1
    check "(forall i -> ([ A[i], 7, 92, A[i] ] | 1..2))[2]" (array_dense [(1,2)] [|7;92|]) // 2 ∈ bound(A)
    check "(forall i -> ([ A[i], 7, 92, A[i] ] | 1..2))[8]" (array_dense [(1,2)] [|7;92|]) // 8 ∉ bound(A)

    check "bound(forall i -> ([ ?, 7, 92, ? ] | 1..2))" All_1
    check "bound(forall i -> ([ ?, 7, 92, ? ] | 0..2))" All_1

    // <-----------------------------------------------------------------------------

    // example from the spec
    let check3 = check_expr_ctx "
        bound_d : Bound (int,int,int,int)
        d : Array (int,int,int,int) int

        bound_d = (1..2,4..5,7..9,9..11)
        d = [ (1000*y_1 + 100*y_2 + 10*y_3 + y_4) : (y_1,y_2,y_3,y_4) in bound_d ]
    "

    let b1 = Bound (1,2)
    let b2 = Bound (4,5)
    let b3 = Bound (7,9)
    let b4 = Bound (9,11)
    let prod = Bound [All_1; b1; meet b3 b4]

    check3 "bound(forall (x_1,x_2,x_3) -> d[x_2,4,x_3,x_3])" prod    // c = 4 (in b2)
    check3 "bound(forall (x_1,x_2,x_3) -> d[x_2,6,x_3,x_3])" Empty_3 // c = 6 (not in b2)
    check3 "bound(forall (x_1,x_2,x_3) -> d[x_2,6,x_2,x_3])" Empty_3 // bound on x_2 = b1 ⊓ b3 = empty
    check3 "bound(forall x -> d[x-3,x,x+3,x+6])" b2

[<Fact>]
let ``forall with sparse bounds`` () =
    let check expr exp_val =
        check_expr_ctx "
            A : Array int int
            B : Array (int,int,int) int

            A = [ 3:17, 5:27, 10:19 ]
            B = [ (1,1,1):1, (1,2,2):2, (1,2,3):3, (2,2,2):4, (2,3,4):5, (3,4,5):6 ]
        " expr exp_val

    check "bound(forall i -> A[i])" (Bound [3;5;10])
    check "bound(forall i -> A[4])" (error 1) // A[4] is independent of i and evaluates to ERROR

    check "bound(forall (i,j) -> B[1,i,j])" (Bound (List.map Index [[1;1];[2;2];[2;3]]))
    check "bound(forall (i,j) -> B[1,j,i])" (Bound (List.map Index [[1;1];[2;2];[3;2]]))
    check "bound(forall (i,j) -> B[i,2,j])" (Bound (List.map Index [[1;2];[1;3];[2;2]]))
    check "bound(forall (i,j) -> B[j,2,i])" (Bound (List.map Index [[2;1];[3;1];[2;2]]))
    check "bound(forall (i,j) -> B[i,j,7])" Empty_2
    check "bound(forall (i,j) -> B[i,2,7])" Empty_2
    check "bound(forall (i,j) -> B[i,3,3])" Empty_2 // no element has last two components = 3
    check "bound(forall (i,j) -> B[7,7,7])"    (error 2) // B[7,7,7] is independent of i and j and evaluates to ERROR
    check "bound(forall (i,j) -> B[i,j,A[0]])" (error 2) // A[0] is independent of i and j and evaluates to ERROR

    check "bound(forall (i,j) -> B[1,i,i])" (Bound (2, List.map Index [[1];[2]], [0])) // nothing limits j
    check "bound(forall (i,j) -> B[1,j,j])" (Bound (2, List.map Index [[1];[2]], [1])) // nothing limits i
    check "bound(forall (i,j) -> B[1,j,j])" (Bound (2, List.map Index [[1];[2]], [1])) // nothing limits i

    check "bound(forall i -> B[1,i,i])" (Bound [1;2])
    check "bound(forall i -> B[i,i,i])" (Bound [1;2])

    check "bound(forall (i,j) -> B[i,j,j])" (Bound (List.map Index [[1;1];[1;2];[2;2]]))
    // Like the previous one, except that the second term further limits j to be 2
    check "bound(forall (i,j) -> B[i,j,j] + B[i,j,2])" (Bound (List.map Index [[1;2];[2;2]]))

    // test with affine transformations of the index
    check "bound(forall i -> A[-i])"    (Bound [-3;-5;-10])
    check "bound(forall i -> A[3*i])"   (Bound [1]) // 3*1 = 3 ∈ bound(A)
    check "bound(forall i -> A[2*i])"   (Bound [5]) // 2*5 = 10 ∈ bound(A)
    check "bound(forall i -> A[2*i+1])" (Bound [1;2]) // { 2*1+1, 2*2+1 } = { 3,5 } ⊂ bound(A)
    check "bound(forall i -> A[4*i])"   Empty_1
    check "bound(forall i -> B[i,i+1,i+1+0])"      (Bound [1])
    check "bound(forall i -> B[i-7,i-3-3,-7+i+1])" (Bound [8])
    check "bound(forall i -> B[i+0,i+1,i+1+1])"    (Bound [1;2;3])
    check "bound(forall i -> B[2,-i,i+4])"         (Bound [-2]) // -(-2) = -2 + 4 = 2
    check "bound(forall i -> B[2*i+1,i*i,2*(i+1)+1])" (Bound [0;1]) // corresponds to {(1,2,3), (3,4,5)} ⊂ bound(B)
    check "bound(forall i -> B[-2*i,-3*i,-2*(i-1)])"  (Bound [-1])  // corresponds to {(2,3,4)} ⊂ bound(B)
    check "bound(forall i -> B[2*i,i*i,2*i+1])" Empty_1
    check "bound(forall (i,j) -> B[i,j+1,1+j+1])"  (Bound (List.map Index [[1;1];[2;2];[3;3]]))
    check "bound(forall (i,j) -> B[i,2*j,i*j])" (Bound (List.map Index [[1;1];[2;1];[3;2]])) // corresponds to {(1,2,2), (1,2,3), (2,2,2), (3,4,5)} ⊂ bound(B)
    check "bound(forall (i,j) -> B[2*i,5*j,2*i+1])" Empty_2
    check "bound(forall (i,j,k) -> B[-2*i,-3*i,-2*(i-1)])" (Bound (3, [Index [-1]], [0])) // corresponds to {(2,3,4)} ⊂ bound(B) (nothing limits j or k)
    check "bound(forall (j,i,k) -> B[-2*i,-3*i,-2*(i-1)])" (Bound (3, [Index [-1]], [1])) // -"-
    check "bound(forall (j,k,i) -> B[-2*i,-3*i,-2*(i-1)])" (Bound (3, [Index [-1]], [2])) // -"-

[<Fact>]
let ``forall with predicate bounds`` () =
    // the arrays are "inlined" because it's not valid to assign infinite arrays to variables
    let check1 expr exp_val = check_expr (sprintf expr "[ 100 * i : i : 1 <= i && i <= 10 ]") exp_val
    let check2 expr exp_val = check_expr (sprintf expr "[ 10 * i + j : (i,j) : i <= j ]") exp_val

    check1 "member(-5, bound(forall i -> %s[i+5]) )" false
    check1 "member(-4, bound(forall i -> %s[i+5]) )" true
    check1 "member( 0, bound(forall i -> %s[i+5]) )" true
    check1 "member( 5, bound(forall i -> %s[i+5]) )" true
    check1 "member( 6, bound(forall i -> %s[i+5]) )" false

    // this should be { (a,b) : a >= b }
    check2 "member((3,4), bound(forall (i,j) -> %s[j,i]))" false
    check2 "member((4,3), bound(forall (i,j) -> %s[j,i]))" true

    // i <= i is always true, so the bound should become "all" (or the predicate equivalent of it)
    check2 "member(-20, bound(forall i -> %s[i,i]) )" true
    check2 "member( 10, bound(forall i -> %s[i,i]) )" true
    check2 "member(100, bound(forall i -> %s[i,i]) )" true

    // i <= i - 1 is never true, so the bound should become empty
    check2 "member(-20, bound(forall i -> %s[i,i-1]) )" false
    check2 "member( 10, bound(forall i -> %s[i,i-1]) )" false
    check2 "member(100, bound(forall i -> %s[i,i-1]) )" false

    // this should be { i : i >= 14 }
    check2 "member( 13, bound(forall i -> %s[17,i+3]) )" false
    check2 "member( 14, bound(forall i -> %s[17,i+3]) )" true
    check2 "member(100, bound(forall i -> %s[17,i+3]) )" true

    // i <= 2 * trunc(i/2) is true negative numbers and even non-negative numbers
    check2 "member(-2, bound(forall i -> %s[i,i/2*2]) )" true
    check2 "member(-1, bound(forall i -> %s[i,i/2*2]) )" true
    check2 "member( 0, bound(forall i -> %s[i,i/2*2]) )" true
    check2 "member( 1, bound(forall i -> %s[i,i/2*2]) )" false
    check2 "member( 2, bound(forall i -> %s[i,i/2*2]) )" true
    check2 "member( 3, bound(forall i -> %s[i,i/2*2]) )" false

[<Fact>]
let ``Nested arrays in forall expressions`` () =
    let check = check_expr_ctx "
        A : Array int (Array int (Array int float))
        B : Array int float
        B = [ 1.0, 7.0 ]
        A = [ 10.. : [ B, B, B ], [ B, B, B ], [ B, B, B ], [ B, B, B ] ]
    "
    // In this example we have:
    // bound(A) = 10..13
    // bound(A[j]) = 0..2 for all j ∈ bound(A)
    // bound(A[j][k]) = 0..1 for all j ∈ bound(A) and k ∈ bound(A[j])

    // first level -----------------------------------------------
    check "bound(forall i -> A[i][0][0])" (Bound (10,13))
    // even though the access here will be out-of-bounds for all i, 10..13 is the correct (over-approximate) answer:
    check "bound(forall i -> A[i][100][100])" (Bound (10,13))
    // the second level of indexing is ignored, since A[i] doesn't have a constant bound, even
    // though a more exact result would be "empty":
    check "bound(forall i -> A[i][i][100])"   (Bound (10,13))

    // second level -------------------------------------------------
    check "bound(forall i -> A[10][i][0])"     (Bound (0,2))
    check "bound(forall i -> A[10][i][-1000])" (Bound (0,2))
    check "bound(forall i -> A[10][i][i])"     (Bound (0,2))

    // third level --------------------------------------------
    check "bound(forall i -> A[10][0][i])" (Bound (0,1))

    check "bound(forall (i,j,k) -> A[i][j][k])" (Bound [Bound (10,13); All_1; All_1]) // (10..13,all,all)

[<Fact>]
let ``Special handling of boolean expressions in forall body`` () =
    let check expr exp_val =
        check_expr_ctx "
            A, B, C : Array int int

            A = [ i % 2 : i in 1..10 ]
            B = [ 3 * i % 2 : i in 6..15 ]
            C = [ 5 * i % 2 : i in 4..18 ]

        " expr exp_val

    let bound_A = Bound (1,10)
    let bound_B = Bound (6,15)
    let meet_AB = Bound (6,10)

    check "bound(forall i -> if((A[i] = 1 && B[i] = 1) || B[i] = 0, 123, 456))" meet_AB
    // with the following permutations of the condition, if B[i] = 0 then the true branch is ataken
    // and A[i] doesn't need to be evaluated
    check "bound(forall i -> if(B[i] = 0 || (A[i] = 1 && B[i] = 1), 123, 456))" bound_B
    check "bound(forall i -> if(B[i] = 0 || (B[i] = 1 && A[i] = 1), 123, 456))" bound_B
    check "bound(forall i -> if((B[i] = 1 && A[i] = 1) || B[i] = 0, 123, 456))" bound_B

    // The following are the same as the last three except A[i] is used in the true branch. This
    // only "helps" in the first one, because if B[i] is neither 0 nor 1 then the false branch is
    // taken in the other two and A[i] doesn't need to be evaluated.
    check "bound(forall i -> if(B[i] = 0 || (A[i] = 1 && B[i] = 1), 123 * A[i], 456))" meet_AB
    check "bound(forall i -> if(B[i] = 0 || (B[i] = 1 && A[i] = 1), 123 * A[i], 456))" bound_B
    check "bound(forall i -> if((B[i] = 1 && A[i] = 1) || B[i] = 0, 123 * A[i], 456))" bound_B

    check "bound(forall i -> if(A[i] = 1 && B[i] = 1, 123, 456 * B[i]))" (Bound (6,10))

    // (bound(A) ⊓ bound(B)) ⊔ (bound(A) ⊓ bound(C)) =
    //     = (1..10 ⊓ 6..15) ⊔ (1..10 ⊓ 4..18)
    //     = 6..10 ⊔ 4..10
    //     = 4..10
    check "bound(forall i -> (A[i] = 1 || B[i] = 1) && C[i] = 1)" (Bound (4,10))

[<Fact>]
let ``Dense bounds in forall body`` () =
    // in these tests, the forall variable is restricted based on the fact that for a dense bound
    // l..u, it must hold that l ≤ u, and for an explicit dense array with m elements
    // [ l..u : e1,...,em ], it must hold that u - l + 1 = m.
    // (The slicing with 1..10 is just to get a finite bound.)
    check_expr "bound(forall i -> join(i..5, 1..i) | 1..10)" (Bound [1..5]) // -∞..5 ⊓ 1..∞ = 1..5
    check_expr "bound(forall i -> [ i..i+1 : 78,79 ] | 1..10)"  (Bound (1,10)) // holds for all i
    check_expr "bound(forall i -> [ (i..i+1, 2..3) : 78,79; 80,81 ] | 1..10)"  (Bound (1,10)) // holds for all i
    check_expr "bound(forall i -> [ i..2 : 78,79 ] | 1..10)" (Bound (1,1)) // holds only for i = 1
    check_expr "bound(forall i -> [ (5..5+i, i..2) : 78,79; 80,81 ] | 1..10)" (Bound (1,1)) // holds only for i = 1
    check_expr "bound(forall i -> [ i..i : 78,79 ] | 1..10)" Empty_1 // holds for no i
