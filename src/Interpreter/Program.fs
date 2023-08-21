open Parser_Wrapper
open Value

[<EntryPoint>]
let main file_names =
    try
        let stopwatch = System.Diagnostics.Stopwatch.StartNew ()
        let result =
            let programs = file_names |> Array.choose Parse_From_File_and_Print_Errors
            // proceed if all programs were parsed without errors
            if programs.Length = file_names.Length then
                let mutable pipe : Value list = []
                // the pipe is a FIFO queue, so `in_func' always reads the oldest value
                let in_func (type_ : AST.Type) : Value =
                    match pipe with
                    | [] ->
                        Error ("The input stream was empty", false, type_)
                    | h::_ when h.Type <> type_ ->
                        let msg = sprintf "A value of type %s was expected, but a value of type %s was read from the input stream" type_.Str h.Type.Str
                        Error (msg,false,type_)
                    | h::t ->
                        pipe <- t
                        h
                // execute all but the last program and write their outputs to the pipe
                for i in 0..programs.Length-2 do
                    // a program should never read its own output from the pipe,
                    // so it is written to the pipe after the program has terminated
                    let mutable outputs = []
                    let out_func _ value : unit =
                        outputs <- value :: outputs
                    printf "Executing %s..." file_names[i]
                    Interpreter.execute_prog in_func out_func programs[i] |> ignore
                    printfn ""
                    pipe <- pipe @ List.rev outputs
                // execute the last program, but print its output to the console instead
                let out_func (expr : AST.Expr) (value : Value) : unit =
                    Pretty_Print.PP_Expr_N (printf "%s") expr
                    printf " = "
                    let val_str = value.Str
                    if String.exists ((=) '\n') val_str then printfn ""
                    printfn "%s\n" val_str
                printfn "Executing %s..." (Array.last file_names)
                Interpreter.execute_prog in_func out_func (Array.last programs) |> ignore
                0
            else -1
        stopwatch.Stop()
        printfn "Execution time: %f msec" stopwatch.Elapsed.TotalMilliseconds
        result
    with
    | exc ->
        printfn "The following error occurred during execution:\n\n%s." exc.Message
        -1

