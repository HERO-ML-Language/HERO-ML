module Test_static

open Xunit
open Tests_Common

open Parser_Wrapper

// the first element of `lines' should be a source code line, and the remaining lines should consist
// of "---" or "^" markings to highlight expected static errors on the first line
let check_static_errors (context : string) (lines : string list) =
    let src = lines.Head
    let highlights = lines.Tail
    // parse the first line, and for any errors generated extract the range of column numbers
    let columns =
        Parse_From_String (String.concat "\n" [context;src])
        |> snd
        |> List.map (fun error -> (error.Src.Start.Column, error.Src.End.Column))
    // turn `highlights' into ranges of column numbers
    let exp_columns =
        highlights
        |> List.map (fun hl ->
            let i1 = hl |> Seq.findIndex ((<>) ' ')
            let i2 = hl |> Seq.findIndexBack ((<>) ' ')
            if hl[i1] = '-' then
                // "---" marking
                (i1,i2+1)
            else
                // "^" marking for zero-width range
                assert (hl[i1] = '^')
                assert (i1 = i2)
                (i1,i2))
        |> List.sort
    Assert.Equal<(int * int) list>(exp_columns, columns)

[<Fact>]
let ``Parser`` () =
    // it is an error give an empty program
    check_static_errors "" [
        "  ";
        "  ^"]

[<Fact>]
let ``Arithmetic`` () =
    let check = check_static_errors "
        x : int
        y : float
        z : bool
        a : Array int int
        b : Array int float"

    check ["x = true";
           "--------"]
    check ["x = 1 + 2"]
    check ["y = 1 + 2."]
    check ["y = 1. + 2"]
    check ["y = 1. + 2."]
    check ["y = -1 + 2."]
    check ["y = --1 + 2."]
    check ["y = -(--1) + 2."]
    check ["x = -(-(1)) + (--2)"]
    check ["x = 1 + 2.";
           "----------"]
    check ["x = 1. + 2";
           "----------"]
    check ["x = true + 2";
           "    ----    "]
    check ["y = true + 2";
           "    ----    ";
           "------------"]
    check ["y = true + 2.";
           "    ----     "]
    check ["x = true + 2.";
           "    ----     ";
           "-------------"]
    check ["x = 1 + true";
           "        ----"]
    check ["y = 1. + true";
           "         ----"]

    check ["z = 1 < 2"]
    check ["z = 1 < 2."]
    check ["z = 1. < 2"]
    check ["z = 1. < 2."]
    check ["x = 1 < 2";
           "---------"]
    check ["z = true < 2";
           "    ----    "]
    check ["z = true < 2.";
           "    ----     "]
    check ["z = 1 < true";
           "        ----"]
    check ["z = 1. < true";
           "         ----"]
    check ["z = [ 1,2,3 ] < [ 1,2,3 ]";
           "    ---------            ";
           "                ---------"]

    check ["z = 1 = 1"]
    check ["z = 1 = 1."]
    check ["z = 1. = 1"]
    check ["z = 1. = 1."]
    check ["z = true = false"]
    check ["z = true = 1";
           "    --------"]
    check ["z = 1 = true";
           "    --------"]
    check ["z = true = 1.";
           "    ---------"]
    check ["z = 1. = true";
           "    ---------"]
    check ["z = [ 1,2,3 ] = [ 1,2,3 ]";
           "    ---------            ";
           "                ---------"]

    check ["a = [ 1,2,3 ]"]
    check ["b = [ 1,2,3 ]";
           "-------------"]
    check ["b = [ 1.0, 2.0, 3.0 ]"]
    check ["b = [ 1, 2, 3.0 ]"]
    check ["a = [ 1, 2.0, 3 ]";
           "-----------------"]
    check ["a = [ 1, true, 3 ]";
           "         ----     "]
    check ["a = [ 1.0, true, 3 ]";
           "           ----     ";
           "--------------------"]
    check ["b = [ 1, true, 3.0 ]";
           "         ----       "]
    check ["a = [ 1, [ 1.5, 2, 2.5 ], 3 ]";
           "         ---------------     "]

[<Fact>]
let ``Explicit arrays`` () =
    // 3-dimensional 2 × 3 × 8 array with implicit 0-based index ranges
    do  let arr = array_dense [(0,1);(0,2);(0,7)] [|1..(2*3*8)|]
        check_expr "[  1, 2, 3, 4, 5, 6, 7, 8;
                       9,10,11,12,13,14,15,16;
                      17,18,19,20,21,22,23,24;;

                      25,26,27,28,29,30,31,32;
                      33,34,35,36,37,38,39,40;
                      41,42,43,44,45,46,47,48;; ]" arr
        check_expr "[ (,,) :
                      1, 2, 3, 4, 5, 6, 7, 8;
                      9,10,11,12,13,14,15,16;
                     17,18,19,20,21,22,23,24;;

                     25,26,27,28,29,30,31,32;
                     33,34,35,36,37,38,39,40;
                     41,42,43,44,45,46,47,48;; ]" arr
        check_expr "[ (..1,,..7) :
                      1, 2, 3, 4, 5, 6, 7, 8;
                      9,10,11,12,13,14,15,16;
                     17,18,19,20,21,22,23,24;;

                     25,26,27,28,29,30,31,32;
                     33,34,35,36,37,38,39,40;
                     41,42,43,44,45,46,47,48;; ]" arr

    // the same 3d array but with other index ranges
    do  let arr = array_dense [(100,101);(10,12);(1,8)] [|1..(2*3*8)|]
        check_expr "[ (100.., ..12, 1..) :
                      1, 2, 3, 4, 5, 6, 7, 8;
                      9,10,11,12,13,14,15,16;
                     17,18,19,20,21,22,23,24;;

                     25,26,27,28,29,30,31,32;
                     33,34,35,36,37,38,39,40;
                     41,42,43,44,45,46,47,48; ]" arr // NOTE: also tests omitting one semicolon after the last element
        check_expr "[ (..101, ..12, ..8) :
                      1, 2, 3, 4, 5, 6, 7, 8;
                      9,10,11,12,13,14,15,16;
                     17,18,19,20,21,22,23,24;;

                     25,26,27,28,29,30,31,32;
                     33,34,35,36,37,38,39,40;
                     41,42,43,44,45,46,47,48 ]" arr // NOTE: also tests omitting all semicolons after the last element

    // 6-dimensional array with one element
    do  let arr = array_dense (List.replicate 6 (0,0)) [|27|]
        check_expr "[ 27 ;;;;; ]" arr

    let chk = check_static_errors ""

    // inconsistent element list
    chk ["out [ 0,0; 0,0,0; 0,0;; 0; 0; 0 ]";
         "           -----                 ";
         "                        -        ";
         "                           -     ";
         "                              -  "]
    // wrong number of dimensions in bound (2 but should be 3 according the element list)
    chk ["out [ (10..,..5) : 0,0,0; 0,0,0;; 0,0,0; 0,0,0;; 0,0,0; 0,0,0;; ]";
         "      ----------                                                 "]
    // wrong number of dimensions in bound and inconsistent element list
    chk ["out [ (,..5) : 0,0,0; 0,0;; 0,0,0,0; 0,0,0; 0,0;; 0,0,0; 0,0,0 ]";
         "      ------                                                    ";
         "                      ---                                       ";
         "                            -------                             ";
         "                            -------------------                 ";
         "                                            ---                 "]
    // if the bound specification is a product then some or all components can be left empty, but it
    // is a syntax error to give empty parentheses
    chk ["out [ () : 27 ]";
         "       -       "]

    // make sure the parser can distinguish between single-element dense and sparse bounds
    // (and that it isn't confused by parentheses)
    check_expr "[ 5..      : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ (5..)    : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ ((5..))  : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ ..5      : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ (..5)    : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ ((..5))  : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ 5..5     : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ (5..5)   : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ ((5..5)) : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ ((5))..5 : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ ((5))..  : 28 ]" (array_dense [(5,5)] [|28|])
    check_expr "[ 5     : 28 ]" (array_sparse_1d [(5,28)])
    check_expr "[ (5)   : 28 ]" (array_sparse_1d [(5,28)])
    check_expr "[ ((5)) : 28 ]" (array_sparse_1d [(5,28)])
    check_expr "[ size(1..5) : 28 ]" (array_sparse_1d [(5,28)])

    // sparse arrays
    check_expr "[ 0:1, 1+1:3, 2*2:5 ]" (array_sparse_1d [(0,1);(2,3);(4,5)])
    chk ["out [ 0:1; 1+1:3, 2*2:5 ]";
         "         -               "] // the ";" should be ","

    // here there should be no parentheses around x, and since this makes the declaration of x
    // invalid there's also a complaint about x not being defined (to the left of the colon)
    chk ["out [ x : (x) in 1..3 ]";
         "      -                ";
         "          ---          "]

    // here the parser doesn't discover that something is wrong with the first index (dense bound
    // missing an upper endpoint and also not being a valid index expression) until it encounters
    // the second colon
    chk ["out [ 1.. : 1, 2:2 ]";
         "      ---           ";
         "         ^          "]

    // this is okay
    check_expr "[ 1..10 : x in 11..20 ]" (array_dense [(11,20)] (Array.replicate 10 (Bound.Bound (1,10))))
    // but this isn't because the element expression is a dense bound missing an upper endpoint.
    // The parser doesn't discover this until it sees the "in" keyword.
    chk ["out [ 1.. : x in 11..20 ]";
         "         ^               "]
