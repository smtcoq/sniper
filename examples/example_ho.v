From SMTCoq Require Import SMTCoq.
From Sniper.orchestrator Require Import Sniper.
From Sniper Require Import tree.
From Sniper Require Import Transfos.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.


Section higher_order.

Variable A B C: Type.
Variable HA : CompDec A.
Variable HB : CompDec B.
Variable HC : CompDec C.

Lemma map_compound : forall (f : A -> B) (g : B -> C) (l : list A), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
induction l; time scope_info. Admitted.

End higher_order.