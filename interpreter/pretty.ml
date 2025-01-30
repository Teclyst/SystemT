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

let kwd ppf s = Format.fprintf ppf "%s" s

let rec pr_exp0 m ppf e =
  match e with
  | CoqInterpreter.BvarT n ->
      Format.fprintf ppf "_%a" ident (to_string (m - nat_to_zt n - Z.one))
  | CoqInterpreter.FvarT x ->
      Format.fprintf ppf "%a" ident (Util.char_list_to_string x)
  | CoqInterpreter.FalseT -> Format.fprintf ppf "true"
  | CoqInterpreter.TrueT -> Format.fprintf ppf "false"
  | _ -> (
      match term_to_zt e with
      | Some n -> Format.fprintf ppf "%a" ident (to_string n)
      | _ -> Format.fprintf ppf "@[<1>(%a)@]" (pr_lambda m) e )

and pr_lambda m ppf f =
  match f with
  | CoqInterpreter.AbsT e ->
      Format.fprintf ppf "@[<1>%a%a%a@ %a@]" kwd "fun _" ident (to_string m) kwd
        " ->"
        (pr_lambda (m + one))
        e
  | e -> pr_app m ppf e

and pr_app m ppf e = Format.fprintf ppf "@[<2>%a@]" (pr_other_applications m) e

and pr_other_applications m ppf e =
  match e with
  | CoqInterpreter.AppT (e, f) ->
      Format.fprintf ppf "%a@ %a" (pr_app m) e (pr_exp0 m) f
  | CoqInterpreter.PlT e -> Format.fprintf ppf "p1 %a" (pr_exp0 m) e
  | CoqInterpreter.PrT e -> Format.fprintf ppf "p2 %a" (pr_exp0 m) e
  | CoqInterpreter.ST e -> (
      match term_to_zt e with
      | Some n -> Format.fprintf ppf "%a" ident (to_string (n + one))
      | _ -> Format.fprintf ppf "s %a" (pr_exp0 m) e )
  | CoqInterpreter.RecT (e, f, g) ->
      Format.fprintf ppf "rec %a@ %a@ %a" (pr_exp0 m) e (pr_exp0 m) f
        (pr_exp0 m) g
  | CoqInterpreter.PairT (e, f) ->
      Format.fprintf ppf "(%a,@ %a)" (pr_lambda m) e (pr_lambda m) f
  | CoqInterpreter.IteT (e, f, g) ->
      Format.fprintf ppf "@[<2>if %a@, then %a@, else %a@]" (pr_lambda m) e
        (pr_lambda m) f (pr_lambda m) g
  | f -> pr_exp0 m ppf f

let print e =
  pr_lambda zero Format.std_formatter e ;
  Format.pp_print_flush Format.std_formatter ()

let print_endline e = print e ; print_newline ()
