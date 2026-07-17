From SMTCoq Require Import SMTCoq.
From Sniper Require Import Sniper.
From Stdlib Require Import String ZArith Bool Lists.List.
Import ListNotations.


Section higher_order.

Variable A B C: Type.
Variable HA : CompDec A.
Variable HB : CompDec B.
Variable HC : CompDec C.

Lemma map_compound : forall (f : A -> B) (g : B -> C) (l : list A), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
induction l; time scope_info. Abort.

End higher_order.
