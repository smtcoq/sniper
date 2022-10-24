Require Import List.

(** Specification of this file: 
giving an inductive relation I of (implicit) parameters A1, ... Aj,
and of arity l (parameters excluded)
with constructors c_i of type 
forall (xi1 : Bi1), ..., (xin : Bin), 
Pi1 xi1 ... xin -> ... -> Pik xi1 ... xin ->
I (fi1 xi1 ... xin) ... (fil xi1 ... xin),
we linearize the conclusion I (f1 xi1 ... xin) ... (fl xi1 ... xin), which means that we remove 
all the duplicates among the xis and all mentions of A1, ... Aj 
at an index position 
We suppose that all the Pis are inductive relations with no higher-order or dependent types
We suppose that all the functions fis are only made of applied constructors or functions 
and do not depend on each other
All the types Bi1, ... Bin should be datatypes or types variables
and they are not dependent types

Let us take an example with the addition written in a relational way:

Inductive add : nat -> nat -> nat -> Prop :=
| add0 : forall n, add 0 n n
| addS : forall n m k, add n m k -> add (S n) m (S k).

The plugin constructs:

Inductive add_linear : nat -> nat -> nat -> Prop :=
| add0_linear : forall n n', n = n' -> add_linear 0 n n
| addS_linear : forall n m k, add_linear n m k -> add_linear (S n) m (S k).

The linearization can be made in two ways: 
- linearize_default_eq will add propositionnal equalities between the fresh variables
- linearize_bool_eq will add boolean equalities between the fresh variables. 
It should be used with an environment registering (possibly parametric) boolean equalities for 
all the arguments. Whenever a decidable equality should occur on a type variable, 
it will scan the parameters of the inductive to see if one of it is a hypothesis of decidablity

Let us take another example :

Inductive Add (A : Type) (a : A) : list A -> list A -> Prop :=
    Add_head : forall l : list A, Add a l (a :: l)
  | Add_cons : forall (x : A) (l l' : list A),
               Add a l l' -> Add a (x :: l) (x :: l').

The default linearization is the only one to work without further assumptions 
(or without instantiating the A) because we need a decidable equality on A.
But if we consider:

Inductive Add' (A : Type) (HA : has_boolean_eq A) (a : A) : list A -> list A -> Prop :=
    Add_head' : forall l : list A, Add' HA a l (a :: l)
  | Add_cons' : forall (x : A) (l l' : list A),
               Add' HA a l l' -> Add' HA a (x :: l) (x :: l').

Then we get:

Inductive Add'_linear (A : Type) (HA: has_boolean_eq A) (a : A) : list A -> list A -> Prop :=
    Add_head'_linear : forall l l' : list A, eq_dec A a a' -> eq_dec ((fun x (Hx : eq_dec x)
=> eq_dec (list x)) A HA) l l' ->
 Add'_linear a l (a' :: l')
  | Add_cons'_linear : forall (x  x' : A) (l l' : list A), eq_dec HA x x' ->
               Add'_linear a l l' -> Add'_linear a (x :: l) (x :: l').



 *)