# Automatic decision of Inductive Relations

This transformation is divided in 5 files and it is presented 
as a separated plugin called `Decide`.

* File: `theories/deciderel/add_hypothesis_on_parameters.v`
* File: `theories/deciderel/compdec_plugin.v`
* File: `theories/deciderel/linearize_plugin.v`
* File: `theories/deciderel/generate_fix.v`
* File: `theories/deciderel/proof_correctness.v`

These files provide `Coq` vernacular commands but no tactic.

## What does the transformation do? 

Some inductives relations (`Coq` inductives whose codomain
is $Prop$) are inductively-defined whereas there are decidable.

The transformation transforms a subset of the decidable inductive relations into an equivalent function whose return type is `bool`. A `Ltac2` proof script tries to generate the proof of the equivalence and if it fails, the proof is left to the user.

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

Each constructor of these decidable relations should have a
conclusion which mentions *every* constructor variable in order to the transformation to be applicable.

For instance, this constructor (for the typing relation in the simply-typed lambda-calculus) is not in the scope of the
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

In addition, in the current state of the plugin, if you want to generate an equivalent function, each type mentionned by the inductive relation (except $Prop$) must be a member of a specific typeclass from the `SMTCoq` plugin called `CompDec`.

Indeed, decidable equalities are often required during the transformation and the `CompDec` types are also member of the `EqDec` typeclass. Furthermore, the main purpose of this transformation is to be useful for `SMTCoq`, so it relies on its typeclasses.

An improvement would be to replace `CompDec` by `EqDec` and to ask for decidable equalities on the fly (during the [linearization](#linearization) procedure).

## Add hypothesis on parameters

Suppose given $P: Type \to Type$ and an inductive $I$ of type 
$\forall \overrightarrow{(A_{i}: Type)},\; B$.

The purpose of this file is to transform an inductive $I$ quoted in `MetaCoq`
into $I': \; \forall \overrightarrow{(A_{i}: Type) (H_{A_{i}}: \; P \; A_{i})}, \; B$, still quoted.

## CompDec Plugin

The `SMTCoq` plugin relies heavily on the `CompDec` typeclass
(see [here](https://github.com/smtcoq/smtcoq/blob/coq-8.13/src/classes/SMT_classes.v#L148)): 
each type on which a proof is built in `SMTCoq` should belong to this typeclass (types of this typeclass are inhabited, are well-ordered and have a decidable equality `eqb_of_compdec`). 

The file `theories/deciderel/compdec_plugin.v` instantiates 
the previous predicate $P$ by `CompDec`. It will generate in the global environement the inductive $I'$ (so unquoted).

For each concrete type `T` mentioned by the inductive, a proof `HT` of `CompDec T` will be researched in the global environment, and the pair 
`(T, HT)` will be registered and used later (for the linearization step may need it).

## Linearization

The linearization procedure is required as `Coq`'s pattern matching 
always introduces *fresh* pattern variables.

As the fixpoint which decides our inductive relation $I$ will perfom *pattern matching* on the variables that occurs in the conclusion of the constructors of $I$, we need a *linear* conclusion.

Consider the following inductive relation:

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

Thus, the file `linearize_plugin.v` creates a new relation `mem_linear` 
in the global environment:


```
Inductive mem_linear : 
    nat -> list nat -> Prop :=
| MemMatch_linear n n' l :
    eqb_of_compdec nat_compdec n n' ->
        mem_linear n (n'::l)
| MemRecur_linear n n' l : mem_linear n l ->
        mem_linear n (n' :: l).
```

A new variable `n'` is introduced to replace an occurence of `n` in the conclusion, and the two variables are supposed to be equal. 

As we have previously registered proofs of `CompDec nat` thanks to the ["compdec plugin"](#compdec-plugin), we have at our disposal the proof `nat_compdec` which has to be the first argument of `eqb_of_compdec` (the decidable equality of the `CompDec` typeclass).

## Generation of fixpoint

Taking the linearized version of $I$, say, $I_{linear}$, 
the purpose of this file is to generate the equivalent fixpoint in `bool`.

It relies on an unification algorithm: each variable given to the fixpoint 
is destructed by pattern matching until a case which unifies with a conclusion of a constructor of $I_{linear}$ is reached. Then, either the conjonction of the premises should hold, or we continue the algorithm for the other constructors of $I_{linear}$.

To go back to our `mem` example, the fixpoint generated is the following:

```
Fixpoint mem_dec (n: nat) (l : list nat) : bool :=
    match l with
      | [] => false (* no constructor of mem_linerar has [] for second argument in its conclusion *)
      | x :: xs => eqb_of_compdec x n || (* first constructor *)
          mem_dec n xs (* second constructor *)
    end.
```

The `TemplateMonad` of `MetaCoq` is used to define vernacular commands
to build the fixpoints.

In this file, the available commands are:

`MetaCoq Run (build_fixpoint_auto I_linear l)`

Here, `l` is a list of triple of decidable inductive relations, their boolean version and the proof of their equivalence in the `term` inductive type of `MetaCoq` quoted terms. 

Indeed, some inductive relations may mention other inductive relations, and in its current state the plugin is not able to decide them recursively.

There is also the command:

`MetaCoq Run (build_fixpoint_recarg I_linear l n)`

Indeed, our plugin may not be able to find the structurally decreasing 
argument automatically, so it should be provided by the user in some cases.

The last command is:

`MetaCoq Run (linearize_and_fixpoint_auto I l).`

which also perfoms the linearization step.


## Proof of equivalence

The main command of this file `theories/proof_correctness.v` is:

`MetaCoq Run (decide I l).`

When it succeeds, it generates automatically the fixpoint version `I_linear_decidable` of `I`,
and a proof of equivalence between `I` and `I_linear_decidable`.

Because of `MetaCoq`'s `TemplateMonad` limitations (there is no way of catching an exception, so it is not possible to handle a failure case when the proof cannot be generated automatically), the proof is only printed. That is, if the proof is called `decidable_proof` the user should write:

```
Next Obligation.
exact decidable_proof.
Qed.
```
in order to define it in the global environment.

If the `Ltac2` proof script fails, the user can write its own proof of equivalence thanks to:

```
Next Obligation.
my_proof_script.
Qed.
```

In particular, whenever some kind of strong induction is required, the proof script will fail. 

It is the case for the `even` predicate, for instance, as the induction step of the proof with weak induction will ask 
for `even (S n)` knowing only `even n` whereas we would have needed 
to be asked to prove
`even (S (S n))` knowing `even n`.
