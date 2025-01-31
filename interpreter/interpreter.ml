let rec loop (fenv : CoqInterpreter.termT CoqInterpreter.FMap.t) : unit =
  ( try
      print_string "\x1B[1;35mSystemT > \x1B[0m";
      Format.pp_print_flush Format.std_formatter ();
      let input = input_line stdin in
      let buf = Lexing.from_string input in
      match Parser.entry Lexer.token buf with
      | Ast.Expr e ->
          let e = Ast.convert fenv [] e in
          let e = CoqInterpreter.par_fsubst fenv e in
          print_string ("\x1B[3;34m_ =\x1B[0m ");
          Format.pp_print_flush Format.std_formatter ();
          Pretty.print_endline (CoqInterpreter.reduce e) ;
          loop fenv
      | Ast.Bind (x, e) ->
          let e = Ast.convert fenv [] e in
          let e = CoqInterpreter.par_fsubst fenv e in
          let e = CoqInterpreter.reduce e in
          print_endline ("\x1B[3;34mval\x1B[0m " ^ x ^ " \x1B[3;34m=\x1B[0m ");
          Format.pp_print_flush Format.std_formatter ();
          Pretty.print_endline (CoqInterpreter.reduce e) ;
          loop (CoqInterpreter.FMap.add (Util.string_to_char_list x) e fenv)
      | Ast.Quit ->
        print_endline "\x1B[3;34mQuitting.\x1B[0m";
        exit 0
    with
  | Lexer.LexerError s -> print_endline ("\x1B[1;31mLexing Error! \x1B[0m" ^ s)
  | Parser.Error -> print_endline "\x1B[1;31mSyntax Error!\x1B[0m"
  | Util.NameError s -> print_endline ("\x1B[1;31mSyntax Error! \x1B[0;31m'" ^ s ^ "'\x1B[3;31m is unbound, yet starts with a \x1B[0;31m'_'\x1B[3;31m.\x1B[0m")
  | Util.UnknownError s -> print_endline ("\x1B[1;31mUnknown Reference! \x1B[0;3;31mUnknown value \x1B[0;31m'" ^ s ^ "'\x1B[3;31m.\x1B[0m") ) ;
  loop fenv

let () =
  print_endline "\x1B[3;34mThis is the SystemT REPL.\x1B[0m";
  loop CoqInterpreter.FMap.empty
