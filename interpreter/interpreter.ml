let rec loop (env : CoqInterpreter.termT CoqInterpreter.FMap.t) : unit =
  ( try
      let input = input_line stdin in
      let buf = Lexing.from_string input in
      print_newline () ;
      match Parser.entry Lexer.token buf with
      | Ast.Expr e ->
          let e = Ast.convert [] e in
          let e = CoqInterpreter.par_fsubst env e in
          Pretty.print_endline (CoqInterpreter.reduce e) ;
          loop env
      | Ast.Bind (x, e) ->
          let e = Ast.convert [] e in
          let e = CoqInterpreter.par_fsubst env e in
          let e = CoqInterpreter.reduce e in
          loop (CoqInterpreter.FMap.add (Util.string_to_char_list x) e env)
      | Ast.Quit -> exit 0
    with
  | Lexer.LexerError s -> print_endline s
  | Parser.Error -> print_endline "Syntax error!"
  | Util.NameError s -> print_endline ("Invalid name " ^ s ^ "!") ) ;
  loop env

let () = loop CoqInterpreter.FMap.empty
