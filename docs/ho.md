# Prenex higher-order

This transformation is defined in the file `theories/higher_order.v`

## What does this transformation do?

This transformation is a very simple encoding of some higher-order features, in order to avoid complex encodings when they are not needed. It works only when there are higher-order functions taking concrete functions as arguments.

For any higher-order application `f g`, the transformation poses the definition `f_g := f g`
and folds the definition of `f_g` in order to hide the higher-order feature.

In addition, it adds and proves the propositionnal equality `f_g = f g` in the local context.

## An example

```
1 goal
A : Type
B : Type
C : Type
l : list A
f : A -> B
g : B -> C
______________________________________(1/1)
map g (map f l) = map (fun x : A => g (f x)) l

prenex_higher_order.

1 goal
A : Type
B : Type
C : Type
l : list A
f : A -> B
g : B -> C
f0 := map g : list B -> list C
f1 := map f : list A -> list B
f2 := map (fun x : A => g (f x)) : list A -> list C
H : f0 =
    (fix map (l : list B) : list C :=
       match l with
       | [] => []
       | a :: t => g a :: map t
       end)
H0 : f1 =
     (fix map (l : list A) : list B :=
        match l with
        | [] => []
        | a :: t => f a :: map t
        end)
H1 : f2 =
     (fix map (l : list A) : list C :=
        match l with
        | [] => []
        | a :: t => g (f a) :: map t
        end)
______________________________________(1/1)
f0 (f1 l) = f2 l
```

