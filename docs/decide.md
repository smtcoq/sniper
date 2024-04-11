# Automatic decision of Inductive Predicates

This transformation is divided in 5 files and it is presented 
as a separated plugin called `Decide`.

* File: `theories/deciderel/add_hypothesis_on_parameters.v`
* File: `theories/deciderel/compdec_plugin.v`
* File: `theories/deciderel/linearize_plugin.v`
* File: `theories/deciderel/generate_fix.v`
* File: `theories/deciderel/proof_correctness.v`

These files provide `Coq` vernacular commands but no tactic.

## What does the transformation do? 

Some inductives predicates (`Coq` inductives whose codomain
is $Prop$) are inductively-defined whereas there are decidable.

The transformation transforms a subset of the decidable inductive predicates into an equivalent function whose return type is `bool`. A `Ltac2` proof script tries to generate the proof of the equivalence and if it fails, the proof is left to the user.

Example:

```
Inductive even (n: nat) : Prop :=
| evenO : even 0
| evenSucc n : even n -> even (S (S n)).
```

is transformed into 

```
Fixpoint even_dec (n: nat) : bool :=
    match n with
      | 0 => true
      | 1 => false
      | S (S n') => even_dec n'
    end.
```

Each constructor of these decidable predicates should have a
conclusion which mentions *every* constructor variable in order to the transformation to be applicable.

For instance, this constructor (for the typing predicate in the simply-typed lambda-calculus) is not in the scope of the
transformation:

```
Inductive has_type : env -> term -> typ -> Prop  :=
...
| typ_app G A B t u : 
    has_type G t (Arrow A B) ->
    has_type G u A ->
    has_type G (App t u) B
...
```

Indeed, the variable `A` does not occurs in the conclusion 
`has_type G (App t u) B`.

In addition, in the current state of the plugin, if you want to generate an equivalent function, each type mentionned by the inductive predicate (except $Prop$) must be a member of a specific typeclass from the `SMTCoq` plugin called `CompDec`.

Indeed, decidable equalities are often required during the transformation and the `CompDec` types are also member of the `EqDec` typeclass. Furthermore, the main purpose of this transformation is to be useful for `SMTCoq`, so it relies on its typeclasses.

An improvement would be to replace `CompDec` by `EqDec` and to ask for decidable equalities on the fly (during the [linearization](#linearization) procedure).

## Add hypothesis on parameters

Suppose given $P: Type \to Type$ and an inductive $I$ of type 
$forall \overrightarrow{(A_{i}: Type)},\; B$.

The purpose of this file is to transform an inductive $I$ quoted in `MetaCoq`
into $I': \; forall \overrightarrow{(A_{i}: Type) (H_{A_{i}}: \; P \; A_{i})}, \; B$, still quoted.

## CompDec Plugin

The `SMTCoq` plugin relies heavily on the `CompDec` typeclass: 
each type on which a proof is built in `SMTCoq` should belong to this typeclass (types of this typeclass are inhabited, are well-ordered and have a decidable equality `eqb_of_compdec`). 

The file `theories/deciderel/compdec_plugin.v` instantiates 
the previous predicate $P$ by `CompDec`. It will generate in the global environement the inductive $I'$ (so unquoted).

For each concrete type `T` mentioned by the inductive, a proof `HT` of `CompDec T` will be researched in the global environment, and the pair 
`(T, HT)` will be registered and used later (for the linearization step may need it).

## Linearization

The linearization procedure is required as `Coq`'s pattern matching 
always introduces *fresh* pattern variables.

As the fixpoint which decides our inductive predicate $I$ will perfom *pattern matching* on the variables that occurs in the conclusion of the constructors of $I$, we need a *linear* conclusion.

Consider the following inductive predicate:

```
Inductive mem : nat -> list nat -> Prop :=
| MemMatch n l : mem n (n::l)
| MemRecur n n' l : mem n l -> mem n (n' :: l).
``` 

Its equivalent boolean fixpoint is *NOT*:

```
Fixpoint mem_dec (n: nat) (l : list nat) : bool :=
    match l with
      | [] => false
      | n :: xs => true
      | x :: xs => mem n xs
    end
```

The second occurence of `n` replaces the first occurence and is *NOT* the same variable. 

We need to linearize the conclusion of `mem`.

Thus, the file `linearize_plugin.v` creates a new predicate `mem_linear` 
in the global environment:


```
Inductive mem_linear : 
    nat -> list nat -> Prop :=
| MemMatch_linear n n' l :
    eqb_of_compdec nat_compdec n n' ->
        mem_linear n (n'::l)
| MemRecur_linear n n' l : mem_linear n l 
    -> mem_linear n (n' :: l).
```

A new variable `n'` is introduced to replace an occurence of `n` in the conclusion, and the two variables are supposed to be equal. 

As we have previously registered proofs of `CompDec nat` thanks to the ["compdec plugin"](#compdec-plugin), we have at our disposal the proof `nat_compdec` which has to be the first argument of `eqb_of_compdec` (the decidable equality of the `CompDec` typeclass).

## Generation of fixpoint

## Proof of equivalence