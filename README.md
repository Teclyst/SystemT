# SystemT

## Author

Matteo Wei.

## Overview

An attempt to formalize Gödel's System-T using the _Coq_ (_Rocq_?) proof assistant, for **Alexis Saurin**'s _Functional Programming and Formal Proofs in Coq_ course at LMFI.

In particular, the main goal of this project is to prove strong normalization for System-T.

The project also contains an attempt to certify a type-checking algorithm, and an interpreter with a REPL for a mini-language of higher-order primitive recursive functions.

## Building the project

- To build all _Coq_ and _OCaml_ files, run

  ```{bash}
  dune build
  ```

- To run the REPL executable (once the project is built), run

  ```{bash}
  _build/default/interpreter/interpreter.exe
  ```

- To delete all build files, run

  ```{bash}
  dune clean
  ```
