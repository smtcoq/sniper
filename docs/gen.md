# Generation Principle

This transformation is available in two different versions, 
in two separated files:

* The file `theories/case_analysis_existentials.v` for the version with *existentials*
quantifiers
* The file `theories/case_analysis.v` for the version with the 
*projection functions*

## What does this transformation do?

This transformation takes an *algebraic datatype* `I`
not applied to its parameters (an inductive type made of non dependent sums 
or products whose codomain is `Type` or `Set`) 
and states and proves its *generation principle*, that is, 
each term `t : I` comes from one of its constructors.

If we have the following `Coq` definition (`S` is either
`Set` or `Type`):

```
Inductive I (a1 : A1) ... (an : An) : S :=
| c1 :  T11 -> ... -> T1k -> I a1 ... an 
...
| cl : Tl1 -> ... -> Tlk -> I a1 ... an
```

then, the generation principle for `I` *with existentials* would be:

$\forall (\overrightarrow{a_{i} : A_{i}}) (t :  I \; \vec{a_{i}}), \;
\exists (\overrightarrow{x_{1_{i}}: T_{1_{i}}}), \;
t = c_{1} \; \vec{x_{1_{i}}} \lor ... \lor
\exists (\overrightarrow{x_{l_{i}}: T_{l_{i}}}),
t = c_{l} \; \vec{x_{l_{i}}}$.

The tactic is `gen_statement_existentials I H`, where `I` is the 
inductive and `H` a fresh name.

The version *without* existentials uses the projections functions $p_{u_{v}}$, each of
of type $\forall (\overrightarrow{a_{i} : A_{i}})
(t :  I \; \vec{a_{i}}) (d_{u_{v}}: T_{u_{v}}),  T_{u_{v}}$

such that 
$p_{u_{v}} \; \vec{a_{i}} \; d_{u_{v}} \; (c_{u} \; \overrightarrow{x_{u_{i}}}) = x_{u_{v}}$
and $p_{u_{v}} \; \vec{a_{i}} \; d_{u_{v}}  \; t = d$ otherwise.

In other words, the projection function $p_{u_{v}}$ returns 
either the $v$-th value of the constructor $u$, or a default value.

With the projections, the generation statement becomes:

$\forall (\overrightarrow{a_{i} : A_{i}}) (t :  I \; \vec{a_{i}}) \overrightarrow{(d_{i_{j}} : T_{i_{j}})}, \;
t = c_{1} \; \overrightarrow{p_{1_{i}} \; \vec{a_{i}} \; d_{1_{i}} \; x_{1_{i}}} \lor ... \lor
t = c_{l} \; \overrightarrow{p_{l_{i}} \; \vec{a_{i}} \; d_{l_{i}} \; x_{l_{i}}}$.

The tactic is `pose_gen_statement I`, with `I` the inductive we are 
interested in. The projections functions are added in the local context 
but their bodies are cleared.

## Why do we need a statement without existentials?

The main backend of `Sniper` is the `SMTCoq` plugin, which does not handle existentials. 

For this reason, in order to help `SMTCoq` to perform case analysis on terms from an algebraic datatype, the generation principle should be stated without existentials. 

Furthermore, all terms on which `SMTCoq` is able to reason should be part of a typeclass in which all types are inhabited. Indeed, `SMTCoq` uses the `Array` theory, for which a default value is required. 

For this reason, the presence of default values required in the projection functions is not a problem: once the statement is monomorphized, we can instantiate each of them by a canonical inhabitant.

## An example

* Generation principle for lists with existentials:

```
forall (A : Type) (t : list A),
    t = [] \/ (exists (x : A) (xs : list A), t = x :: xs)
```

* The generation principle for list with projections will add 
these variables in the local context:

```
proj0: forall (A : Type), A -> list A -> A
proj1: forall (A : Type), list A -> list A -> list A
gen_list: forall (A : Type) (l ld : list A) (d : A),
    l = [] \/ l = proj0 A a l :: proj1 A ld l
```


