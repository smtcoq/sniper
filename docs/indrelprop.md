# Inductive Relations in Prop

This transformation is defined in the file `theories/indrel.v`.

## What does this transformation do?

It is designed for intuitionnistic external backend that may not have access to the definition of some inductive relation `I` 
(that is, an inductive whose codomain is $Prop$).

This transformation has no use for `SMTCoq` but it can be useful for other backends (work in progress...).

The transformation adds and proves the definition of the constructors of `I` and the inversion principle of `I`
in the local context.

## An example

Suppose that we have this inductive:

```
Inductive Add {A : Type} (a : A) : list A -> list A -> Prop :=
  | Add_head : forall l : list A, Add a l (a :: l)
  | Add_cons : forall (x : A) (l l' : list A),
               Add a l l' -> Add a (x :: l) (x :: l').
```

Then, running the tactic `inversion_principle @Add`
will add these hypothesis in the local context:

```
Add_head0 : forall (A : Type) (a : A) (l : list A),
            Add a l (a :: l)
Add_cons0 : forall (A : Type) (a x : A) (l l' : list A),
            Add a l l' -> Add a (x :: l) (x :: l')
Hinv : forall (A : Type) (a : A) (l l' : list A),
        Add a l l' <->
        (exists l'' : list A, l = l'' /\ l' = a :: l'') \/
        (exists (x : A) (l1 l2 : list A),
           Add a l1 l2 /\ l = x :: l1 /\ l' = x :: l2)
```


