Inductive even : nat -> Prop :=
even0 : even 0
| evenSS : forall n, even n -> even (S (S n)).

Fixpoint even_decidable (H : nat) : bool :=
  match H with
  | 0 => true
  | S _ => false
  end || match H with
         | S (S x0) => even_decidable x0
         | _ => false
         end.

Fixpoint even_decidable_or_integrated (H : nat) : bool :=
  match H with
  | 0 => true || false
  | S H => (match H with
         | (S x0) => even_decidable_or_integrated x0
         | _ => false
         end) || false
end.


Lemma bar P : false = true -> P.
Proof. intro H. inversion H. Qed.

Fixpoint even_decidable_imp_even (n : nat) : even_decidable n = true -> even n :=
match n return even_decidable n = true -> even n with 
| 0 => fun _ => even0
| S n' => match n' with
    | 0 => fun H => bar _ H
    | S n'' => fun H => evenSS n'' (even_decidable_imp_even n'' H)
    end
end.

Require Import List.
Import ListNotations.

Inductive smaller2 : list nat -> list nat -> Prop :=
    sm_nil2 : forall l : list nat, smaller2 [] l
  | sm_cons2 : forall (x x' : nat) (l l' : list nat),
              smaller2 l l' -> smaller2 (x :: l) (x' :: l').

Fixpoint smaller2_decidable 
(H H0 : list nat) {struct H} : bool :=
  match H with
  | [] => true
  | _ :: _ => false || match H with
     | [] => false
     | _ :: x0 =>
         match H0 with
         | [] => false
         | _ :: x2 => smaller2_decidable x0 x2
         end
     end
end.

Fixpoint smaller2_decidable_is_correct (l : list nat) : forall l', smaller2_decidable l l' = true -> smaller2 l l' :=
match l return (forall l', smaller2_decidable l l' = true -> smaller2 l l')  with
| [] => fun l' _ => sm_nil2 l'
| x :: xs => fun l' => match l' return smaller2_decidable (x::xs) l' = true -> smaller2 (x::xs) l' with
            | [] => fun H => bar _ H
            | x' :: xs' => fun H => sm_cons2 x x' xs xs' (smaller2_decidable_is_correct xs xs' H) 
            end
end.

Require Import ZArith.

Inductive elt_list :=
 |Nil : elt_list
 |Cons : Z -> Z -> elt_list -> elt_list.

Inductive Inv_elt_list : Z -> elt_list -> Prop :=
 | invNil  : forall b, Inv_elt_list b Nil
 | invCons : forall (a b  j: Z) (q : elt_list),
     (j <= a)%Z -> (a <= b)%Z ->  Inv_elt_list (b+2) q ->
     Inv_elt_list j (Cons a b q).

Fixpoint Inv_elt_list_decidable (H : Z) (H0 : elt_list) {struct H0} : bool :=
  match H0 with
  | Nil => true
  | Cons x x0 x1 =>
         Inv_elt_list_decidable (x0 + 2)%Z x1 && ((x <=? x0)%Z && (H <=? x)%Z)
end.

Require Import Bool.

Search and. 

Search Z.le Z.leb. (* proj2 (Zle_is_le_bool proj2 (proj1 (andb_prop _ _ (proj1 (andb_prop _ _ H))))) *)  

Check true&&(false&&true).

(* andb_prop
     : forall a b : bool,
       a && b = true -> a = true /\ b = true 
andb_prop _ _ H : (Inv_elt_list_decidable (b + 2) e' && a <=? b) = true /\ z <=? a = true
andb_prop _ _ (proj1 (andb_prop _ _ H)) : Inv_elt_list_decidable (b + 2) e' = true /\ a <=? b
proj1 (andb_prop _ _ (proj1 (andb_prop _ _ H))) : Inv_elt_list_decidable (b+2) e' = true 
proj2 (andb_prop _ _ (proj1 (andb_prop _ _ H))) : a <=? b 
proj2 (andb_prop _ _ H) : z <=? a = true

*)

Fixpoint Inv_elt_list_decidable_is_correct (z : Z) (e : elt_list) :
Inv_elt_list_decidable z e = true -> Inv_elt_list z e :=
match e return (Inv_elt_list_decidable z e = true -> Inv_elt_list z e) with
| Nil => fun _ => invNil z
(* H : Inv_elt_list_decidable z (Cons a b e') = true 
 H : Inv_elt_list_decidable (b + 2) e' && a <=? b  && z <=? a *)
| Cons a b e' => fun H => invCons a b z e'
(Zle_bool_imp_le _ _ (proj2 (andb_prop _ _ (proj2 (andb_prop _ _ H)))))
(Zle_bool_imp_le _ _ (proj1 (andb_prop _ _ (proj2 (andb_prop _ _ H)))))
(Inv_elt_list_decidable_is_correct (b+2) e' (proj1 (andb_prop _ _ H)))
end.











