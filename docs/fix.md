# Elimination of anonymous fixpoints

This transformation is defined in the file `theories/elimination_fixpoints.v`.

## What does this transformation do?

This transformation `eliminate_fix_hyp`, takes as an argument a hypothesis `H` whose type
contains an anonymous fixpoint of the form `fix f_anon (x1: A1) ... (xn: An) := ...`.

It looks in the global environment of Coq and in the local context to see if there is 
a constant `f` or a local definition `f := ...` which reduces to this anonymous fixpoint by delta-reduction.

Similarly, it also looks if a *generalization* of `fix f_anon ...` (a constant which reduces to `fun x1 ... xn => fix f_anon ... := ...`) is convertible to a constant.

The tactic transforms `H` into a new hypothesis of the same identifier `H`, in which each occurence of the anonymous fixpoint in its own body is replaced by the definition discovered. 
In addition, a step of beta-reduction is made if possible (that is, if the function is applied to some arguments).

This transformation is written using the plugin [coq-elpi](https://github.com/LPCIC/coq-elpi), and the proof of each application of the transformation is a `Ltac` proof.

There is a version `eliminate_fix_cont` taking an additional argument: a `Ltac` continuation, 
which can bind the transformed hypothesis `H`.

## An example

```
Goal (forall (H : forall (A: Type) (l : A), @length A l =
             (fix length (l : list A) : nat :=
                match l with
                | [] => 0
                | _ :: l' => S (length l')
                end) A l) -> False). intros.

1 goal
H : forall (A: Type) (l : A), @length A l =
             (fix length (l : list A) : nat :=
                match l with
                | [] => 0
                | _ :: l' => S (length l')
                end) A l
______________________________________(1/1)
False

eliminate_fix_hyp H.

1 goal

H : forall (A : Type) (l : list A),
    length l =
       match l with
       | [] => 0
       | _ :: l' => S (length l')
       end
______________________________________(1/1)
False
```

In this example, the anonymous fixpoint `(fix length (l : list A) := ...` is **not** convertible to `length`
as it is applied to the type variable `A`, but its abstraction over `A` is.