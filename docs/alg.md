# Algebraic Datatypes

The corresponding `Coq` file is `/theories/interpretation_algebraic_types.v`.

## What does this transformation do?

This transformation, called `interp_alg_types`, 
takes as an argument an inductive type `I` (not applied to its eventual parameters). 
It will fail if the inductive type is not an algebraic datatype 
(that is, a datatype which can be encoded as a combination of sum types and product types), 
or if the datatype is applied to some parameter.
For instance, `interp_alg_types (list nat)` will fail (because of the parameter), 
`interp_alg_types list` will succeed, and `interp_alg_types True` will fail 
(because `True` is not an algebraic datatype). 

The transformation generates and proves in the local context:

* The *non-confusion principle*: each constructor of `I` is disjoint
* The *injectivity of constructors*: each constuctor of `I` is injective

The *generation principle* is dealt with in two separated files for technical reasons (see [Generation Principle](gen.md)).

The transformation is written in `MetaCoq` and each application is proved thanks to a `Ltac` proof script.

## An example

The transformation `interp_alg_types list` will generate 
and prove:

```
H1 : forall (A : Type) (x : A) (xs : list A),
    [] = x :: xs -> False
H2 : forall (A : Type) (x x' : A) (xs xs' : list A),
    x :: xs = x' :: xs' -> x = x' /\ xs = xs'
```