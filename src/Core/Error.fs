module Error

open Source_Ref

type Error (src : Source_Ref, message : string) =
    member this.Src = src
    member this.Message = message

    override this.ToString () = sprintf "%s: %s" this.Src.Str_S this.Message

let make_error msg_fmt =
    Printf.kprintf (fun (msg : string) (src : Source_Ref) -> Error (src,msg)) msg_fmt
