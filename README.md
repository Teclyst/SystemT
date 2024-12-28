# System-T

## Overview

An attempt to formalize Gödel's System-T using the _Coq_ (_Rocq_?) proof assistant, for **Alexis Saurin**'s _Functional Programming and Formal Proofs in Coq_ course at LMFI.

In particular, the main goal of this project is to prove strong normalization for System-T.

## Building the project

- To build all _Coq_ files, run

  ```{bash}
  make
  ```

- To build documentation, run

  ```{bash}
  make build-doc
  ```

  A `documentation` directory will then be created with `html` formatted versions of the source files.

- To do build both source files and documentation, run

  ```{bash}
  make all
  ```

- To delete all build files, run

  ```{bash}
  make clean
  ```
