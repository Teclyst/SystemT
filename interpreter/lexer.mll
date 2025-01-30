{

  open Parser
  open Util

  exception LexerError of string

  let keywords : token StringMap.t =
    StringMap.of_list [
      ("let", LET);
      ("fun", FUN);
      ("p1", PR1);
      ("p2", PR2);
      ("true", TRUE);
      ("false", FALSE);
      ("if", IF);
      ("then", THEN);
      ("else", ELSE);
      ("s", S);
      ("rec", REC)
    ]
  
  let symbols : token StringMap.t =
    StringMap.of_list [
      ("+", ADD);
      ("=", EQ);
      ("->", ARROW);
      (",", COMMA)
    ]

}

let digit = ['0' - '9']
let letter = ['a' - 'z' 'A' - 'Z' '_']
let ident = letter (letter | digit) *
let symbchar = [',' '-' '>' '=' '+']

rule token = parse
  | [' ' '\t' '\n'] +
    { token lexbuf }
  | eof {
    EOF
  }
  | "#quit" {
    QUIT
  }
  | ident as id {
      match StringMap.find_opt id keywords with
      | Some t -> t
      | _ -> IDENT id
    }
  | [ '0' ] | [ '1' - '9' ] digit * as s {
      NAT (Z.of_string s)
    }
  | [ '0' ] digit * {
      raise (LexerError ("Unexpected leading zeros."))
    }
  | '(' {
    LPAR
  }
  | ')' {
    RPAR
  }
  | symbchar + as id {
      match StringMap.find_opt id symbols with
      | Some t -> t
      | _ -> raise (LexerError ("foo Unexpected token '" ^ id ^ "'."))
    }
  | _ as c
    { raise (LexerError ("Unexpected token '" ^ (String.make 1 c) ^ "'.")) }
