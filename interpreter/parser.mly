%{

  open Ast

%}

%token EOF QUIT

%token <string> IDENT
%token LPAR RPAR

%token FUN ARROW ADD
%token COMMA
%token PR1 PR2
%token TRUE FALSE
%token IF THEN ELSE
%token S
%token <Z.t> NAT
%token REC
%token LET EQ

%nonassoc ELSE ARROW
%left ADD

%start <entry> entry

%%

expr_comma_list:
  | e = expr; COMMA; f = expr {
    Pair (e, f)
  }
  | l = expr_comma_list; COMMA; f = expr {
    Pair (l, f)
  }

atom:
  | x = IDENT {
    Var x
  }
  | FALSE {
    False
  }
  | TRUE {
    True
  }
  | n = NAT {
    Nat n
  }
  | LPAR; e = expr; RPAR {
    e
  }
  | LPAR; l = expr_comma_list; RPAR {
    l
  }

app_expr:
  | e = atom {
    e
  }
  | e = app_expr; f = atom {
    App (e, f)
  }
    | PR1; e = atom {
    Pl e
  }
  | PR2; e = atom {
    Pr e
  }
  | S; e = atom {
    S e
  }
  | REC; e = atom; f = atom; g = atom {
    Rec (e, f, g)
  }

expr:
  | e = app_expr {
    e
  }
  | FUN; p = IDENT *; ARROW; e = expr {
    List.fold_right (fun x e -> Abs(x, e)) p e
  } 
  | IF; e = expr; THEN; f = expr; ELSE; g = expr {
    Ite (e, f, g)
  }
  | e = expr; ADD; f = expr {
    Add (e, f)
  }

entry:
  | LET; x = IDENT; p = IDENT *; EQ; e = expr; EOF {
    Bind (x, List.fold_right (fun x e -> Abs(x, e)) p e)
  }
  | e = expr; EOF {
    Expr e
  }
  | QUIT; EOF {
    Quit
  }