open Z

let ( + ) = add

let ( - ) = sub

let rec nat_to_zt n =
  match n with
  | CoqInterpreter.O -> zero
  | CoqInterpreter.S n -> nat_to_zt n + one

let rec term_to_zt e =
  match e with
  | CoqInterpreter.OT -> Some zero
  | CoqInterpreter.ST e -> Option.map (( + ) one) (term_to_zt e)
  | _ -> None

let ident ppf s = Format.fprintf ppf "%s" s

let rec printf_atom m ppf e =
  match e with
  | CoqInterpreter.BvarT n ->
      Format.fprintf ppf "_%a" ident (to_string (m - nat_to_zt n - Z.one))
  | CoqInterpreter.FvarT x ->
      Format.fprintf ppf "%a" ident (Util.char_list_to_string x)
  | CoqInterpreter.PairT _ as e ->
      Format.fprintf ppf "( @[<hov>%a@])" (printf_tuple m) e
  | CoqInterpreter.FalseT -> Format.fprintf ppf "false"
  | CoqInterpreter.TrueT -> Format.fprintf ppf "true"
  | _ -> (
      match term_to_zt e with
      | Some n -> Format.fprintf ppf "%a" ident (to_string n)
      | _ -> Format.fprintf ppf "( %a)" (printf_expr m) e )

and printf_expr m ppf e =
  match e with
  | CoqInterpreter.AbsT _ ->
      Format.fprintf ppf "fun @[<hov -2>%a@]" (printf_abs m) e
  | CoqInterpreter.PlT e -> Format.fprintf ppf "p1 %a" (printf_atom m) e
  | CoqInterpreter.PrT e -> Format.fprintf ppf "p2 %a" (printf_atom m) e
  | CoqInterpreter.ST e -> (
      match term_to_zt e with
      | Some n -> Format.fprintf ppf "%a" ident (to_string (n + one))
      | _ -> Format.fprintf ppf "s %a" (printf_atom m) e )
  | CoqInterpreter.RecT (e, f, g) ->
      Format.fprintf ppf "rec %a@ %a@ %a" (printf_atom m) e (printf_atom m) f
        (printf_atom m) g
  | CoqInterpreter.IteT (e, f, g) ->
      Format.fprintf ppf "@[<hov> if %a@ then %a@ else %a@]" (printf_expr m) e
        (printf_expr m) f (printf_expr m) g
  | _ -> Format.fprintf ppf "@[<2>%a@]" (printf_app m) e

and printf_tuple m ppf e =
  match e with
  | CoqInterpreter.PairT (e, f) ->
      Format.fprintf ppf "%a,@ %a" (printf_tuple m) e (printf_expr m) f
  | _ -> printf_expr m ppf e

and printf_abs m ppf e =
  match e with
  | CoqInterpreter.AbsT (CoqInterpreter.AbsT _ as e) ->
      Format.fprintf ppf "_%a@ %a" ident (to_string m) (printf_abs (m + one)) e
      | CoqInterpreter.AbsT e ->
        Format.fprintf ppf "_%a ->@ %a" ident (to_string m) (printf_abs (m + one)) e
  | _ -> printf_expr m ppf e

and printf_app m ppf e =
  match e with
  | CoqInterpreter.AppT (e, f) ->
      Format.fprintf ppf "%a@ %a" (printf_app m) e (printf_atom m) f
  | _ -> printf_atom m ppf e

let print e =
  printf_expr zero Format.std_formatter e ;
  Format.pp_print_flush Format.std_formatter ()

let print_endline e = print e ; print_newline ()
