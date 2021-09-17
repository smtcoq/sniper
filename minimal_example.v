
Add Rec LoadPath "/home/louise/github.com/louiseddp/sniper" as Sniper.
Require Import Sniper.Sniper.
Require Import List. 


Section foo. 
Variable A : Type.
Variable HA : CompDec A.

 Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof.
 scope. Abort.

Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof.
intros l a. interp_alg_types (list A).

Abort.


