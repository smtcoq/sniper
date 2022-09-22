This is the source code accompanying the submission entitled
"Compositional pre-processing for automated reasoning in dependent type
theory". It is the property of its authors.


# Build
## Using docker
This is the simplest way of building the code. Simply run:
```bash
docker build -t paper24 -f paper24.docker .
```

You can then access the image through a shell using
```bash
docker run -ti --rm -e DISPLAY=host.docker.internal:0 paper24 bash
```
or through coqide using
```bash
docker run --net=host --env="DISPLAY" --volume="$HOME/.Xauthority:/home/coq/.Xauthority:rw" paper24 coqide
```
For the latter, you may need to set the `DISPLAY`, e.g. by doing `export
DISPLAY=:0` under Linux, or following [these
explanations](https://cntnr.io/running-guis-with-docker-on-mac-os-x-a14df6a76efc)
under MacOS.

## Natively
This procedure has only been tested on Linux.

All the OCaml and Coq source code can be installed in an opam
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
- solvers for the CoqHammer plugin may be installed by following [these
  instructions](https://coqhammer.github.io/#installation-of-first-order-provers)
  (but it is not mandatory).


# Examples
The file `examples/paper_examples.v` is the entry point for the
examples. It presents all the examples of this paper, in the same order;
it is designed to be executed throughout the reading of the paper.

It can be evaluated by running:
```bash
docker run --net=host --env="DISPLAY" --volume="$HOME/.Xauthority:/home/coq/.Xauthority:rw" paper24 coqide /home/coq/paper24/examples/paper_examples.v
```
if you built the code with docker (see above if the display fails), or
```bash
coqide examples/paper_examples.v
```
if you built the code natively.

In the latter case, if you get the error "veriT: not found", or "code
127", it is probably because veriT is not installed in your PATH (see
above).


# Overview
The source code contains:
- all our pre-processing tactics (directories `trakt` and `sniper`);
- a fork of SMTCoq which is aware of `trakt` (directory `smtcoq`);
- the combination of pre-processing tactics and SMTCoq into the `snipe`
  tactic (directory `sniper`);
- examples (directory `examples`; see above).
