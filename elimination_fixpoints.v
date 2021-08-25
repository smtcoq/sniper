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


Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.Template.All.
Require Import utilities.
Require Import definitions.
Require Import expand.
Require Import ZArith.
Require Import String.
Unset Strict Unquote Universe Mode.



(* remove the nth last elements of a list *)
Fixpoint rem_last_elem {A} (n : nat) (l : list A) := match l, n with 
| nil, _ => nil
| cons _ _, 0 => l
| cons x xs, S n' => rem_last_elem n' xs
end.


Definition find_args (t1 t2 : term) := 
match t2 with
| tApp v l => let n:= Datatypes.length l in match t1 with 
        | tApp u l' => (lift n 0 (tApp u (rem_last_elem n l')), v, l)
        | _ => (t1, t2, l)
      end
| _ => (t1, t2, nil)
end.

Fixpoint under_forall_aux (t : term) (l : list (aname*term)) :=
match t with 
| tProd na T u => under_forall_aux u ((na, T)::l)
| _ => (t, l)
end.

Definition under_forall t := under_forall_aux t [].

Fixpoint create_forall (t : term) (l : list (aname*term)) :=
match l with 
| nil => t
| (na, T):: xs => create_forall (tProd na T t) xs
end.

Definition params_eq (t : term) := match t with 
| tApp u l => match l with 
            | [x1; x2; x3] => (u, (x1, x2, x3))
            | _ => (u, (u, u, u))
            end
| _ => (t, (t, t, t))
end.


(* Returns the definition in a fixpoint *)
Definition get_def_in_fix (f: term) := 
match f with 
| tFix l _ => match l with 
          | [] => f
          | x :: xs => x.(dbody)
          end
| _ => f
end.

Definition replace_tFix_by_def (t : term) (def : term) := match t with 
| tFix _ _ => (subst10 def (get_def_in_fix t))
| _ => t
end.


(* replace an anonymous fix by its definition *)
Ltac eliminate_fix_hyp H := 
let T := type of H in let T := metacoq_get_value (tmQuote T) in
let p := eval cbv in (under_forall T) in 
let eq := eval cbv in p.1 in
let list_quantif := eval cbv in p.2 in
let get_info_eq := eval cbv in (params_eq eq) in 
let eq_reif := eval cbv in get_info_eq.1 in 
let A := eval cbv in get_info_eq.2.1.1 in 
let t := eval cbv in get_info_eq.2.1.2 in 
let u := eval cbv in get_info_eq.2.2 in
let prod := eval cbv in (find_args t u) in 
let args := eval cbv in prod.2 in (* the arguments of u *)
let def := eval cbv in prod.1.1 in 
let u_no_app := eval cbv in prod.1.2 in 
let u_no_fix := eval cbv in (replace_tFix_by_def u_no_app def) in
let eq_no_fix := eval cbv in (create_forall (mkEq A t (tApp u_no_fix args)) list_quantif) in
let z := metacoq_get_value (tmUnquote eq_no_fix) in
let H' := fresh in let w := eval hnf in z.(my_projT2) 
in assert (H' :w) 
by (repeat (let x := fresh in intro x ; try (destruct x ; auto))).


Ltac eliminate_fix_ho H := fun k =>
let T := type of H in
let T := metacoq_get_value (tmQuote T) in
let p := eval cbv in (under_forall T) in 
let eq := eval cbv in p.1 in
let list_quantif := eval cbv in p.2 in
let get_info_eq := eval cbv in (params_eq eq) in 
let eq_reif := eval cbv in get_info_eq.1 in 
let A := eval cbv in get_info_eq.2.1.1 in 
let t := eval cbv in get_info_eq.2.1.2 in 
let u := eval cbv in get_info_eq.2.2 in
let prod := eval cbv in (find_args t u) in 
let args := eval cbv in prod.2 in (* the arguments of u *)
let def := eval cbv in prod.1.1 in 
let u_no_app := eval cbv in prod.1.2 in 
let u_no_fix := eval cbv in (replace_tFix_by_def u_no_app def) in 
let eq_no_fix := eval cbv in (create_forall (mkEq A t (tApp u_no_fix args)) list_quantif) in
let z := metacoq_get_value (tmUnquote eq_no_fix) in
let H' := fresh in let w := eval hnf in z.(my_projT2)
in assert (H' :w) 
by (repeat (let x := fresh in intro x ; try (destruct x ; auto))) ; k H' ; clear H.





Section tests.

Goal Nat.add = (fun n m : nat => match n with
                            | 0 => m
                            | S p => S (p + m)
                            end).
Proof.
unfold Nat.add.
Abort.

Goal False.
get_def @Datatypes.length.
get_def Nat.add.
expand_hyp add_def.
eliminate_fix_hyp H.
expand_hyp length_def.
eliminate_fix_hyp H1.
Abort.

Fixpoint search { A : Type } { H : CompDec A } ( x : A ) l :=
match l with
| [] => false
| x0 :: l0 => if eqb_of_compdec H x x0 then true else search x l0
end.




Goal False.
get_def @Datatypes.length.
get_def Nat.add.
let x:= eval unfold search in search in pose x.
get_def @search.
expand_hyp search_def.
eliminate_fix_hyp H.
expand_hyp add_def.
eliminate_fix_ho H ltac:(fun H0 => let t := type of H0 in idtac).
expand_hyp length_def.
eliminate_fix_hyp H.
Abort.



Goal False.
get_def @Datatypes.length.
expand_hyp length_def.
eliminate_fix_hyp H.
get_def Nat.add.
expand_hyp add_def.
eliminate_fix_hyp H1.
Abort.


End tests.



