# Anonymous functions

This transformation is defined in the file `theories/anonymous_functions.v`.

## What does this transformation do?

This transformation takes all the anonymous functions in the local context
of the form `fun (x: T) => ...`, creates a definition `f := fun (x: T) => ...`
and folds the definition of `f`. It also proves and adds the propositional 
equality `f = fun (x: T) => ...` in the local context.

Note that branches in pattern matching are anonymous functions
that you may want to deal with differently, so the transformation avoids them.

## An example

```
1 goal
A : Type
B : Type
C : Type
l : list A
f : A -> B
g : B -> C
H : (fun x : nat => x + 1) 42 = 43
______________________________________(1/1)
map g (map f l) = map (fun x : A => g (f x)) l

anonymous_funs.

1 goal
A : Type
B : Type
C : Type
l : list A
f : A -> B
g : B -> C
f0 := fun x : A => g (f x) : A -> C
H : (fun x : nat => x + 1) 42 = 43
H0 : f0 = (fun x : A => g (f x))
______________________________________(1/1)
map g (map f l) = map f0 l
```

