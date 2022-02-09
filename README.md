# Sniper

`Sniper` is a Coq plugin that provides a new Coq tactic, `snipe`, that
provides general proof automation.

This plugin is an extension of [SMTCoq](https://smtcoq.github.io), a
plugin to safely call external SMT solvers from Coq. `Sniper` extends
SMTCoq by translating (a subset) of Coq goals into first-order logic
before calling SMTCoq.

The translation is implemented through a combination of modular, small
transformations that independently eliminate specific aspects of Coq
logic towards first-order logic. These small transformations are safe,
either generating proof terms on the fly (*certifying* transformations)
or being proved once and for all in Coq (*certified* transformations). A
crucial transformation is given by the
[Trakt](https://github.com/ecranceMERCE/trakt) plugin.

This release is for the submission to the conference Interactive Theorem
Proving 2022.


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

It requires OCaml between 4.09 and 4.10:
```
opam switch create 4.09.1
eval $(opam env)
```

You need to add two opam repositories:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```

Then simply install this version of `Sniper`:
```
opam pin -y add coq-sniper https://github.com/smtcoq/sniper.git#itp22
```

It works with Coq-8.13.

You also need the veriT SMT solver, using [these sources](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz).
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

## Examples, tests and benchmarks

Commented examples are available at ``examples.v``.

The benchmarks are in the `benchs` folder.
You need to install ``coq-hammer`` by running the command
```
opam install coq-hammer
```
Then to test ``snipe`` you can run
```
make bench_snipe
```
To test ``hammer`` you can run 
```
make bench_hammer
```
And to run the tests on both tactics, the command is
```
make bench
```

The other files in this folder are the orginal not automatized ``List`` library (``List_no_automation.v``)
and the outputs obtained by running the benchs on the computer mentioned in the paper.


## License
As an extension of SMTCoq, `Sniper` is released under the same license
as SMTCoq: CeCILL-C. See the file LICENSE for details.


## Authors
See the file [AUTHORS](https://github.com/smtcoq/sniper/blob/master/AUTHORS).
