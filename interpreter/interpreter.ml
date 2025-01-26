open CoqInterpreter

let () =
  Pretty.print_endline
    (reduce
       (AppT (BvarT O, PairT (AbsT OT, PrT (PairT (ST OT, FvarT ['x']))))))
