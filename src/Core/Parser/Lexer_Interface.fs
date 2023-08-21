module Lexer_Interface

// Interface to the lexer for the parser
type Lexer_Interface =
  { Begin_New_Block : unit -> unit
    Renew_Block : unit -> unit
    Clear_Parens : unit -> unit
    Get_Last_Lexeme : unit -> string }
