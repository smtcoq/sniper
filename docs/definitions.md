# Definitions

This transformation is available in the file `theories/definitions.v`.

## What does this transformation do?

This transformation, at an atomic level, is called `get_def` and takes as an argument a Coq constant `c`. 
By delta-reduction, `c` is convertible to its definition `c_def`.
Thus, `get_def c` asserts and proves the propositional equality `H: c = c_def` in the Coq proof context.

## An example

```
Goal False.

(* 1 goal
______________________________________(1/1)
False *)

get_def List.app.

(* 1 goal
app_def : app =
          (fun A : Type =>
           fix app (l m : list A) {struct l} : list A :=
             match l with
             | nil => m
             | a :: l1 => a :: app l1 m
             end)
______________________________________(1/1)
False *)

```