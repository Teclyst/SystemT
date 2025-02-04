exception NameError of string
exception UnknownError of string
exception TypeError of CoqInterpreter.type_error

module StringMap = Map.Make (String)

let char_list_to_string s =
  List.fold_right (fun c s -> String.make 1 c ^ s) s ""

let string_to_char_list s = String.fold_right List.cons s []

let rec int_to_nat n =
  match compare n 0 with
  | 0 -> CoqInterpreter.O
  | 1 -> CoqInterpreter.S (int_to_nat (n - 1))
  | _ -> raise (Invalid_argument "Strictly negative!")

let rec zt_to_nat n =
  match compare n Z.zero with
  | 0 -> CoqInterpreter.O
  | 1 -> CoqInterpreter.S (zt_to_nat (Z.sub n Z.one))
  | _ -> raise (Invalid_argument "Strictly negative!")
