This is the source code accompanying the submission entitled
"Compositional pre-processing for automated reasoning in dependent type
theory". It is the property of its authors.


# Installation
All the OCaml and Coq source code can be easily installed in an opam
switch:
```bash
opam switch create paper24 ocaml-base-compiler.4.09.1
eval $(opam env --switch=paper24)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y .
```

We use automated backends that rely on external theorem provers:
- the SMT solver veriT for the SMTCoq plugin must be installed by
  following [these
  instructions](https://github.com/smtcoq/smtcoq/blob/coq-8.13/INSTALL.md#verit);
- solvers for the CoqHammer plugin can be installed by following [these
  instructions](https://coqhammer.github.io/#installation-of-first-order-provers)
  (but it is not mandatory).


# Examples
The file `examples/paper_examples.v` is the entry point for the
examples. It presents all the examples of this paper, in the same order;
it is designed to be executed throughout the reading of the paper.


# Overview
The source code contains:
- all our pre-processing tactics (directories `trakt` and `sniper`);
- a fork of SMTCoq which is aware of `trakt` (directory `smtcoq`);
- the combination of pre-processing tactics and SMTCoq into the `snipe`
  tactic (directory `sniper`);
- examples (directory `examples`; see above).
