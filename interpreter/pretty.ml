open Z

let ( + ) = add

let ( - ) = sub

let rec nat_to_zt n =
  match n with
  | CoqInterpreter.O -> zero
  | CoqInterpreter.S n -> nat_to_zt n + one

let rec zt_to_alphabet n =
  match n = zero with
  | true -> ""
  | _ ->
      let q, r = div_rem (n - one) (of_int 26) in
      zt_to_alphabet q ^ String.make 1 (Char.chr (Stdlib.( + ) 97 (to_int r)))

let rec termT_to_zt e =
  match e with
  | CoqInterpreter.OT -> Some zero
  | CoqInterpreter.ST e -> Option.map (( + ) one) (termT_to_zt e)
  | _ -> None

let ident ppf s = Format.fprintf ppf "%s" s

let rec printf_typeT_atom ppf t =
  match t with
  | CoqInterpreter.BoolT -> Format.fprintf ppf "bool"
  | CoqInterpreter.NatT -> Format.fprintf ppf "nat"
  | CoqInterpreter.TvarT x ->
      Format.fprintf ppf "'%a" ident (zt_to_alphabet (nat_to_zt x))
  | _ -> Format.fprintf ppf "(%a)" printf_typeT_FunT t

and printf_typeT_FunT ppf t =
  match t with
  | CoqInterpreter.FunT (t, u) ->
      Format.fprintf ppf "%a ->@ %a" printf_typeT_ProdT t printf_typeT_FunT u
  | _ -> Format.fprintf ppf "%a" printf_typeT_ProdT t

and printf_typeT_ProdT ppf t =
  match t with
  | CoqInterpreter.ProdT (t, u) ->
      Format.fprintf ppf "%a *@ %a" printf_typeT_ProdT t printf_typeT_atom u
  | _ -> Format.fprintf ppf "%a" printf_typeT_atom t

let print_typeT t =
  printf_typeT_FunT Format.std_formatter t ;
  Format.pp_print_flush Format.std_formatter ()

let print_endline_typeT t = print_typeT t ; print_newline ()

let rec printf_termT_atom m ppf e =
  match e with
  | CoqInterpreter.BvarT n ->
      Format.fprintf ppf "x%a" ident (to_string (m - nat_to_zt n - Z.one))
  | CoqInterpreter.FvarT x ->
      Format.fprintf ppf "%a" ident (Util.char_list_to_string x)
  | CoqInterpreter.PairT _ as e ->
      Format.fprintf ppf "( @[<hov>%a@])" (printf_termT_PairT m) e
  | CoqInterpreter.FalseT -> Format.fprintf ppf "false"
  | CoqInterpreter.TrueT -> Format.fprintf ppf "true"
  | _ -> (
      match termT_to_zt e with
      | Some n -> Format.fprintf ppf "%a" ident (to_string n)
      | _ -> Format.fprintf ppf "( %a)" (printf_termT_expr m) e )

and printf_termT_expr m ppf e =
  match e with
  | CoqInterpreter.AbsT _ ->
      Format.fprintf ppf "fun @[<hov -2>%a@]" (printf_termT_absT m) e
  | CoqInterpreter.IteT (e, f, g) ->
      Format.fprintf ppf "@[<hov> if %a@ then %a@ else %a@]"
        (printf_termT_expr m) e (printf_termT_expr m) f (printf_termT_expr m) g
  | _ -> Format.fprintf ppf "@[<2>%a@]" (printf_termT_appT m) e

and printf_termT_PairT m ppf e =
  match e with
  | CoqInterpreter.PairT (e, f) ->
      Format.fprintf ppf "%a,@ %a" (printf_termT_PairT m) e
        (printf_termT_expr m) f
  | _ -> printf_termT_expr m ppf e

and printf_termT_absT m ppf e =
  match e with
  | CoqInterpreter.AbsT (CoqInterpreter.AbsT _ as e) ->
      Format.fprintf ppf "x%a@ %a" ident (to_string m)
        (printf_termT_absT (m + one))
        e
  | CoqInterpreter.AbsT e ->
      Format.fprintf ppf "x%a =>@ %a" ident (to_string m)
        (printf_termT_absT (m + one))
        e
  | _ -> printf_termT_expr m ppf e

and printf_termT_appT m ppf e =
  match e with
  | CoqInterpreter.AppT (e, f) ->
      Format.fprintf ppf "%a@ %a" (printf_termT_appT m) e (printf_termT_atom m)
        f
  | CoqInterpreter.PlT e -> Format.fprintf ppf "p1 %a" (printf_termT_atom m) e
  | CoqInterpreter.PrT e -> Format.fprintf ppf "p2 %a" (printf_termT_atom m) e
  | CoqInterpreter.ST e -> (
      match termT_to_zt e with
      | Some n -> Format.fprintf ppf "%a" ident (to_string (n + one))
      | _ -> Format.fprintf ppf "s %a" (printf_termT_atom m) e )
  | CoqInterpreter.RecT (e, f, g) ->
      Format.fprintf ppf "rec %a@ %a@ %a" (printf_termT_atom m) e
        (printf_termT_atom m) f (printf_termT_atom m) g
  | _ -> printf_termT_atom m ppf e

let print_termT e =
  printf_termT_expr zero Format.std_formatter e ;
  Format.pp_print_flush Format.std_formatter ()

let print_endline_termT e = print_termT e ; print_newline ()
