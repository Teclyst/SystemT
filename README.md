# SystemT

## Overview

An attempt to formalize Gödel's System-T using the _Coq_ (_Rocq_?) proof assistant, for **Alexis Saurin**'s _Functional Programming and Formal Proofs in Coq_ course at LMFI.

In particular, the main goal of this project is to prove strong normalization for System-T.

## Building the project

- To build all _Coq_ files, run

  ```{bash}
  dune build
  ```

- To build documentation, run

  ```{bash}
  dune build @doc
  ```

  `html` files will be produced, in subdirectory `_build/default/theories/SystemT.html`.

- To build $\LaTeX$ documentation, run

  ```{bash}
  dune build @doc-latex
  ```

  `tex` files will be produced, in subdirectory `_build/default/theories/SystemT.tex`.

- To delete all build files, run

  ```{bash}
  dune clean
  ```
