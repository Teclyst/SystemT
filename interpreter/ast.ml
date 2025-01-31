type vident = string

type expr =
  | Var of vident
  | Abs of vident * expr
  | App of expr * expr
  | Pair of expr * expr
  | Pl of expr
  | Pr of expr
  | True
  | False
  | Ite of expr * expr * expr
  | O
  | S of expr
  | Nat of Z.t
  | Add of expr * expr
  | Rec of expr * expr * expr

type entry = Expr of expr | Bind of (vident * expr) | Quit

let rec convert (fenv : CoqInterpreter.termT CoqInterpreter.FMap.t) (benv : vident list) (e : expr) : CoqInterpreter.termT =
  match e with
  | Var x -> (
      match List.find_index (( = ) x) benv with
      | Some n -> CoqInterpreter.BvarT (Util.int_to_nat n)
      | _ ->
          match x.[0] = '_', CoqInterpreter.FMap.mem (Util.string_to_char_list x) fenv with
          | true, _ -> raise (Util.NameError x)
          | _, true -> CoqInterpreter.FvarT (Util.string_to_char_list x)
          | _ -> raise (Util.UnknownError x) )
  | Abs (x, e) -> AbsT (convert fenv (x :: benv) e)
  | App (e, f) -> CoqInterpreter.AppT (convert fenv benv e, convert fenv benv f)
  | Pair (e, f) -> CoqInterpreter.PairT (convert fenv benv e, convert fenv benv f)
  | Pl e -> CoqInterpreter.PlT (convert fenv benv e)
  | Pr e -> CoqInterpreter.PrT (convert fenv benv e)
  | True -> CoqInterpreter.TrueT
  | False -> CoqInterpreter.FalseT
  | Ite (e, f, g) ->
      CoqInterpreter.IteT (convert fenv benv e, convert fenv benv f, convert fenv benv g)
  | O -> CoqInterpreter.OT
  | S e -> CoqInterpreter.ST (convert fenv benv e)
  | Nat n -> CoqInterpreter.nat_as_natT (Util.zt_to_nat n)
  | Add (e, f) ->
      CoqInterpreter.AppT
        (CoqInterpreter.AppT (CoqInterpreter.addT, convert fenv benv e), convert fenv benv f)
  | Rec (e, f, g) ->
      CoqInterpreter.RecT (convert fenv benv e, convert fenv benv f, convert fenv benv g)
