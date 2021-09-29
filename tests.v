(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* If you have installed Sniper, change this line into `Require Import Sniper.Sniper`. *)
Require Import Sniper.


Section tests.

Goal ((forall (A : Type) (l : list A),
#|l| = match l with
       | [] => 0
       | _ :: xs => S #|xs|
       end) -> True).
intro H.
eliminate_pattern_matching H.
exact I.
Qed.

Goal ((forall (x : nat) (a : nat) (l : list nat), 
@hd nat x (@cons nat a l) = match (@cons nat a l) with
| nil => x
| y :: xs => y
end)).
def_and_pattern_matching_mono.
assumption.
Qed.

Goal forall (l : list Z) (x : Z),  hd_error l = Some x -> (l <> []).
Proof.
interp_alg_types_context_goal. 
def_and_pattern_matching_mono.     
verit.
Qed.

(* Test polymorphism *) 
Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> ((forall (x1 x2 : bool) (y1 y2 : nat), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : nat) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : bool) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
intro H. inst. split. assumption. split. assumption. assumption.
Qed. 

End tests.
