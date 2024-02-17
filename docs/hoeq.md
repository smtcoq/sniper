# Elimination of higher-order equlities

## What does this transformation do?

This transformation `expand_hyp`, takes as an argument a hypothesis `H` of 
type `f = g`, where `f` or `g` are functions taking `k` arguments. 
Suppose that `T1 ... Tk` are the types of these arguments.

The tactic `expand_hyp` creates a new hypothesis `H'` starting from `H` : 
```
H': forall (x1: T1) ... (xk: Tk), f x1 ... xk = g x1 ... xk
```

There is a version `expand_hyp_cont` taking an additional argument: a `Ltac` continuation, 
which can bind the produced hypothesis `H'`

## An example

```
Goal (forall (length_def :length =
             (fun A : Type =>
              fix length (l : list A) : nat :=
                match l with
                | [] => 0
                | _ :: l' => S (length l')
                end)) -> False). intros.

1 goal
length_def : length =
             (fun A : Type =>
              fix length (l : list A) : nat :=
                match l with
                | [] => 0
                | _ :: l' => S (length l')
                end)
______________________________________(1/1)
False

expand_hyp length_def.

1 goal
length_def : length =
             (fun A : Type =>
              fix length (l : list A) : nat :=
                match l with
                | [] => 0
                | _ :: l' => S (length l')
                end)
H : forall (A : Type) (l : list A),
    #|l| =
    (fix length (l0 : list A) : nat :=
       match l0 with
       | [] => 0
       | _ :: l' => S (length l')
       end) l
______________________________________(1/1)
False
```