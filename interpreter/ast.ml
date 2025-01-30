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

let rec convert (env : vident list) (e : expr) : CoqInterpreter.termT =
  match e with
  | Var x -> (
      match List.find_index (( = ) x) env with
      | Some n -> CoqInterpreter.BvarT (Util.int_to_nat n)
      | _ ->
          if x.[0] = '_' then raise (Util.NameError x)
          else CoqInterpreter.FvarT (Util.string_to_char_list x) )
  | Abs (x, e) -> AbsT (convert (x :: env) e)
  | App (e, f) -> CoqInterpreter.AppT (convert env e, convert env f)
  | Pair (e, f) -> CoqInterpreter.PairT (convert env e, convert env f)
  | Pl e -> CoqInterpreter.PlT (convert env e)
  | Pr e -> CoqInterpreter.PrT (convert env e)
  | True -> CoqInterpreter.TrueT
  | False -> CoqInterpreter.FalseT
  | Ite (e, f, g) ->
      CoqInterpreter.IteT (convert env e, convert env f, convert env g)
  | O -> CoqInterpreter.OT
  | S e -> CoqInterpreter.ST (convert env e)
  | Nat n -> CoqInterpreter.nat_as_natT (Util.zt_to_nat n)
  | Add (e, f) ->
      CoqInterpreter.AppT
        (CoqInterpreter.AppT (CoqInterpreter.addT, convert env e), convert env f)
  | Rec (e, f, g) ->
      CoqInterpreter.RecT (convert env e, convert env f, convert env g)
