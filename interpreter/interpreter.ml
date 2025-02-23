let rec loop (fenv : CoqInterpreter.termT CoqInterpreter.FMap.t)
    (tenv : CoqInterpreter.typeT CoqInterpreter.FMap.t) : unit =
  ( try
      print_string "\x1B[1;35mSystemT > \x1B[0m" ;
      Format.pp_print_flush Format.std_formatter () ;
      let input = input_line stdin in
      let buf = Lexing.from_string input in
      match Parser.entry Lexer.token buf with
      | Ast.Expr e -> (
          let e = Ast.convert fenv [] e in
          match CoqInterpreter.type_check tenv e with
          | Ok t ->
              let e = CoqInterpreter.par_fsubst fenv e in
              let e = CoqInterpreter.reduce e in
              let t = Pretty.rename_type t in
              Format.fprintf Format.std_formatter
                "@[<hov>\x1B[3;34m_ :@,\
                 \x1B[0;32m %a\x1B[3;34m =\x1B[0m@ %a @]\n"
                Pretty.printf_typeT_FunT t
                (Pretty.printf_termT_expr Z.zero)
                e ;
              Format.pp_print_flush Format.std_formatter () ;
              loop fenv tenv
          | Error error -> raise (Util.TypeError error) )
      | Ast.Bind (x, e) -> (
          let e = Ast.convert fenv [] e in
          match CoqInterpreter.type_check tenv e with
          | Ok t ->
              let e = CoqInterpreter.par_fsubst fenv e in
              let e = CoqInterpreter.reduce e in
              let t = Pretty.rename_type t in
              Format.fprintf Format.std_formatter
                "@[<hov>\x1B[3;34mval\x1B[0m %a\x1B[3;34m :@,\
                 \x1B[0;32m %a\x1B[3;34m =\x1B[0m@ %a @]\n"
                Pretty.ident x Pretty.printf_typeT_FunT t
                (Pretty.printf_termT_expr Z.zero)
                e ;
              Format.pp_print_flush Format.std_formatter () ;
              loop
                (CoqInterpreter.FMap.add (Util.string_to_char_list x) e fenv)
                (CoqInterpreter.FMap.add (Util.string_to_char_list x) t tenv)
          | Error error -> raise (Util.TypeError error) )
      | Ast.Quit ->
          print_endline "\x1B[3;34mQuitting.\x1B[0m" ;
          exit 0
    with
  | Lexer.LexerError s -> print_endline ("\x1B[1;31mLexing Error!\n\x1B[0m" ^ s)
  | Parser.Error -> print_endline "\x1B[1;31mSyntax Error!\x1B[0m"
  | Util.UnknownError s ->
      print_endline
        ( "\x1B[1;31mUnknown Reference!\n\x1B[0;3;31mUnknown value \x1B[0;31m'"
        ^ s ^ "'\x1B[3;31m.\x1B[0m" )
  | Util.TypeError
      (CoqInterpreter.Type_error_unification_error
         (CoqInterpreter.Unification_error_different_constructors (t, u)) ) ->
      Format.fprintf Format.std_formatter
        "@[<h>\x1B[1;31mType Error!\n\
         \x1B[0;3;31mCould not unify \x1B[0;31m%a \x1B[3;31mwith \
         \x1B[0;31m%a\x1B[3;31m.\n\
         \x1B[0m@]"
        Pretty.printf_typeT_FunT t Pretty.printf_typeT_FunT u
  | Util.TypeError
      (CoqInterpreter.Type_error_unification_error
         (CoqInterpreter.Unification_error_tvarT_occurs (x, t)) ) ->
      Format.fprintf Format.std_formatter
        "@[<h>\x1B[1;31mType Error!\n\
         \x1B[0;3;31mThe type variable \x1B[0;31m'%a \x1B[3;31moccurs inside \
         \x1B[0;31m%a\x1B[3;31m.\n\
         \x1B[0m@]"
        Pretty.ident
        (Pretty.zt_to_alphabet (Pretty.nat_to_zt x))
        Pretty.printf_typeT_FunT t ) ;
  loop fenv tenv

let () =
  print_endline "\x1B[3;34mThis is the SystemT REPL.\x1B[0m" ;
  loop CoqInterpreter.FMap.empty CoqInterpreter.FMap.empty
