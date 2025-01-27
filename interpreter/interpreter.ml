open CoqInterpreter

let () =
  Pretty.print_endline
    (reduce
       (AppT (fiboT, (ST (ST (ST (ST (ST OT))))))))
