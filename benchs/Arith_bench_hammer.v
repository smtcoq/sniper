From Hammer Require Import Hammer.

Hammer_version.
Hammer_objects.

Require Import ZArith Bool.

(* Easy arith on Z *)
Lemma arith_Z (n m : Z) : (Z.lt n m)%Z \/ (Z.le m n)%Z.
Time try hammer.
Qed.

(* Easy arith on Z, on bool *)
Lemma arith_Z_bool (n m : Z) : (Z.ltb n m)%Z || (Z.leb m n)%Z = true.
Time hammer. 
Qed.

Lemma arith_and_uninterpreted_symbol (T : Type) (x y : nat) (b : bool) (f : nat -> T) :
True /\ b = true \/ f (x + y ) = f (y + x ). 
Time hammer.
Qed.

Lemma example_com (T : Type) (x y : nat) (b : bool) (f : nat -> T) :
True /\ (b = true \/ f (y + x) = f (x + y)).
Time hammer.
Qed.

Lemma example_assoc (T : Type) (x y z : nat) (b : bool) (f : nat -> T) :
True /\ (b = true \/ f ((x + y) + z) = f (x + (y + z))).
Time hammer.
Qed.
