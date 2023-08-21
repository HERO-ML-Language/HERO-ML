module Parser_Wrapper

open Source_Ref
open Error
open AST
open Lexer
open Parser
open FSharp.Text.Lexing
open System.IO

let marked_src_line (src : string) (ref : Source_Ref) : string =
    // fetch the first line of the referenced source code
    let line =
        let line_start = ref.Start.Line_Offset
        let line_end =
            { line_start..src.Length-1 }
            |> Seq.tryFind (fun i -> src[i] = '\n' || src[i] = '\r')
            |> defaultArg <| src.Length
        if ref.Start.Line < ref.End.Line then  // spans multiple lines
            src[line_start..line_end-1] + " ..."
        elif line_end <= ref.Start.Offset then // begins at the line break after the first line
            src[line_start..line_end-1] + " "
        else
            src[line_start..line_end-1]
    // create the underline
    let col_start, col_end = ref.Start.Column, min (ref.End.Offset - ref.Start.Line_Offset) line.Length
    let underline =
        if col_start < col_end then
            // curly underline
            line[0..col_end-1]
            |> String.mapi (fun i c ->
                match c with
                | '\t' -> '\t'
                | _ when col_start <= i -> '~'
                | _ -> ' ')
        else
            // use a single '^' when the reference has length zero
            line[0..col_end]
            |> String.mapi (fun i c ->
                match c with
                | '\t' -> '\t'
                | _ when i = col_start -> '^'
                | _ -> ' ')
    String.concat "\n" [line; underline]

let Parse_From_String_ (ext : bool) (src : string) : Prog option * Error list =
    let file_index =
        lock Source_Ref.sources (fun () ->
            Source_Ref.sources.Add src
            Source_Ref.sources.Count - 1)
    let lexer = Stateful_Lexer (ext,src,file_index)
    let prog, errors = prog lexer.Get_Next_Token lexer.Lex_Buffer_for_Parser |> Type_Analysis.check_prog
    (if errors.IsEmpty then Some prog else None), errors

let Parse_From_String = Parse_From_String_ false
let Parse_From_String_Ext = Parse_From_String_ true

let Parse_From_File_and_Print_Errors_ (ext : bool) (file_name : string) : Prog option =
    let src =
        use text_reader = new StreamReader(file_name)
        text_reader.ReadToEnd()
    let file_index =
        lock Source_Ref.sources (fun () ->
            Source_Ref.sources.Add src
            Source_Ref.sources.Count - 1)
    let lexer = Stateful_Lexer (ext,src,file_index)
    let prog, errors = prog lexer.Get_Next_Token lexer.Lex_Buffer_for_Parser |> Type_Analysis.check_prog
    if errors.IsEmpty then
        Some prog
    else
        errors |> List.iter (fun (error) ->
            printfn "%s: %s.\n\n%s\n" error.Src.Str_S error.Message
                    (marked_src_line src error.Src))
        None

let Parse_From_File_and_Print_Errors = Parse_From_File_and_Print_Errors_ false
let Parse_From_File_and_Print_Errors_Ext = Parse_From_File_and_Print_Errors_ true

let Tokenize_String_ (ext : bool) (src : string) : (token * Position * Position * string) list =
    let file_index =
        lock Source_Ref.sources (fun () ->
            Source_Ref.sources.Add src
            Source_Ref.sources.Count - 1)
    let lexer = Stateful_Lexer (ext,src,file_index)
    let lexbuf = lexer.Lex_Buffer_for_Parser
    let rec helper acc =
        let t = lexer.Get_Next_Token lexbuf
        let p1, p2 = lexbuf.StartPos, lexbuf.EndPos
        let l = lexer.Get_Last_Lexeme ()
        let new_acc = (t,p1,p2,l)::acc
        match t with
        | token.EOF -> List.rev new_acc
        | _ -> helper new_acc
    helper []

let Tokenize_String = Tokenize_String_ false
let Tokenize_String_Ext = Tokenize_String_ true

let Tokenize_File_ (ext : bool) (file_name : string) =
    let src =
        use text_reader = new StreamReader(file_name)
        text_reader.ReadToEnd()
    Tokenize_String_ ext src

let Tokenize_File = Tokenize_File_ false
let Tokenize_File_Ext = Tokenize_File_ true
