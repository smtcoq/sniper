# Monomorphization

This transformation is available in two versions:

* In `theories/instantiate_type.v` you will find the first strategy of instantiation.
* In `theories/instantiate_inductive_pars.v` you will find the second strategy of instantiation.

## What does this transformation do?

The transformation `inst` from `theories/instantiate_type.v`
and the one `elimination_polymorphism` from `theories/instantiate_inductive_pars.v`
both select instances and instantiate hypotheses with prenex polymorphism with these instances.

That is, they instantiate all the statements of the form:

$\forall (A : Type), B$

where $B$ is a proposition.

The `inst` strategy will select all the subterms of type $Type$
in the local context and will create one instance for each subterm. 

The `elimination_polymorphism` strategy will look at all the
ground parameters of inductives $I$ in the local context. 
Suppose that there is the ground parameter $u$ at the argument position $n$ for the inductive $I$

If a type variable $A$ is also used at the $n$-th argument position of $I$, then $u$ is a relevant instance.

## An example


```
H: forall (A : Type) (B : Type) (x x' : A) (y y' : B), 
(x, y) = (x', y') -> x = x'
______________________________________(1/1)
forall (x x': nat) (y y': bool), 
(x, y) = (x', y') -> x = x'

inst.

H1: forall (x x' : nat*bool) (y y' : nat*bool), 
(x, y) = (x', y') -> x = x'
H2: forall (x x' : nat*bool) (y y' : bool), 
(x, y) = (x', y') -> x = x'
H3: forall (x x' : nat*bool) (y y' : nat), 
(x, y) = (x', y') -> x = x'
H4: forall (x x' : nat) (y y' : nat*bool), 
(x, y) = (x', y') -> x = x'
H5: forall (x x' : nat) (y y' : bool), 
(x, y) = (x', y') -> x = x'
H6: forall (x x' : nat) (y y' : nat), 
(x, y) = (x', y') -> x = x'
H7: forall (x x' : bool) (y y' : nat*bool), 
(x, y) = (x', y') -> x = x'
H8: forall (x x' : bool) (y y' : bool), 
(x, y) = (x', y') -> x = x'
H9: forall (x x' : bool) (y y' : nat), 
(x, y) = (x', y') -> x = x' 
______________________________________(1/1)
forall (x x': nat) (y y': bool), 
(x, y) = (x', y') -> x = x'

Undo. elimination_polymorphism.

H1: forall (x x' : nat) (y y' : bool), 
(x, y) = (x', y') -> x = x'
______________________________________(1/1)
forall (x x': nat) (y y': bool), 
(x, y) = (x', y') -> x = x'

```



