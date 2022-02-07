From Sniper Require Import Sniper.

Require Import ZArith Bool.

(* Easy arith on Z *)
Lemma arith_Z (n m : Z) : (Z.lt n m)%Z \/ (Z.le m n)%Z.
Time snipe. 
Qed.

(* Easy arith on Z, on bool *)
Lemma arith_Z_bool (n m : Z) : (Z.ltb n m)%Z || (Z.leb m n)%Z = true.
Time snipe. 
Qed.

Lemma arith_and_uninterpreted_symbol (T : Type) (HT : CompDec T) (x y : nat) (b : bool) (f : nat -> T) :
True /\ b = true \/ f (x + y ) = f (y + x ). 
Time snipe.
Qed.

Lemma example_com (T : Type) (HT : CompDec T) (x y : nat) (b : bool) (f : nat -> T) :
True /\ (b = true \/ f (y + x) = f (x + y)).
Time snipe.
Qed.

Lemma example_assoc (T : Type) (HT: CompDec T) (x y z : nat) (b : bool) (f : nat -> T) :
True /\ (b = true \/ f ((x + y) + z) = f (x + (y + z))).
Time snipe. 
Qed.
