module Source_Ref

// Holds the full contents of each source code file currently loaded
let sources = ResizeArray<string> ()

[<Struct>]
type Loc =
    { Line : int
      Column : int
      Line_Offset : int }

    member this.Offset = this.Line_Offset + this.Column
    member this.Str = sprintf "%d:%d" this.Line this.Column
    override this.ToString () = this.Str

[<Struct>]
type Source_Ref =
    { File_Index : int
      Start : Loc
      End : Loc }

    // String representation on the form
    // "{file name}:{start line}:{start column}-{end line}:{end column}"
    member this.Str_FSE (file_names : string array) =
        String.concat "" [ file_names[this.File_Index]; ":"
                           this.Start.Str; "-"; this.End.Str ]
    // String representation on the form
    // "{file name}:{start line}:{start column}"
    member this.Str_FS (file_names : string array) =
        String.concat ":" [ file_names[this.File_Index]; this.Start.Str ]
    // String representation on the form
    // "{start line}:{start column}-{end line}:{end column}"
    member this.Str_SE =
        String.concat "-" [ this.Start.Str; this.End.Str ]
    // String representation on the form
    // "{start line}:{start column}"
    member this.Str_S = this.Start.Str

    member this.Text =
        let fi = this.File_Index
        if fi >= 0 then
            sources[fi][this.Start.Offset .. this.End.Offset - 1]
        else "(source not available)"

    override this.ToString () = this.Str_SE

    static member merge (a : Source_Ref) (b : Source_Ref) : Source_Ref =
        if a.File_Index <> b.File_Index then
            failwith "Only references to the same file can be merged"
        let start = if a.Start.Offset < b.Start.Offset then a.Start else b.Start
        let end_ = if a.End.Offset > b.End.Offset then a.End else b.End
        { File_Index = a.File_Index
          Start = start
          End = end_ }
