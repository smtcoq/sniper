# sniper

`sniper` is a Coq plugin that provides a new Coq tactic, `snipe`, that
provides general proof automation.

This plugin is an extension of [SMTCoq](https://smtcoq.github.io), a
plugin to safely call external SMT solvers from Coq. `sniper` extends
SMTCoq by translating (a subset) of Coq goals into first-order logic
before calling SMTCoq.

The translation is implemented through a combination of modular, small
transformations that independently eliminate specific aspects of Coq
logic towards first-order logic. These small transformations are safe,
either generating proof terms on the fly (*certifying* transformations)
or being proved once and for all in Coq (*certified* transformations).


## Installation and use

This part describes the steps required to try the `snipe` tactic.

You will need the following packages. The names are those for debian, please adapt as required for your distribution.
- opam: for installing coqide, metacoq and smtcoq
- pkg-config: required for creating an opam switch
- libgtksourceview-3.0-dev: required by coqide
- git: for installing smtcoq through opam
- bison, flex: for compiling veriT

If opam was not installed on your machine you have to initialize it (all the files are confined within ~/.opam):
```
opam init --bare --no-setup
```

The version of metacoq that we use requires ocaml < 4.10 and >= 4.09:
```
opam switch create 4.09.1
```

Snipe requires coq 8.11:
```
opam install coqide.8.11.2
```

Metacoq is available through the `coq-released` opam repository:
```
opam repo add coq-released https://coq.inria.fr/opam/released
```

Snipe requires this version of metacoq:
```
opam install coq-metacoq.1.0~beta2+8.11
```

A [tag of SMTCoq](https://github.com/smtcoq/smtcoq/releases/tag/pxtp21)
is distributed for this tag of `snipe`. Download it and install it as
follows:
```
cd src
./configure.sh
make
make install
```

Sources of the veriT SMT solver are distributed
[here](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz).
Once unpacked, compilation of veriT is as follows:
```
cd veriT9f48a98
./configure
make
```

We need the veriT binary to be in PATH in order for snipe to use it:
```
export PATH="$PATH:$(pwd)"
cd ..
```

This command adds the tools installed by opam to PATH
```
eval $(opam env)
```

We generate the makefile for snipe:
```
coq_makefile -f _CoqProject -o Makefile
```

We build snipe:
```
make
```

Now you can run the examples in coqide:
```
coqide examples.v
```

Have fun!


## License
As an extension of SMTCoq, `sniper` is released under the same license
as SMTCoq: CeCILL-C. See the file LICENSE for details.
