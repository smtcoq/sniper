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


Require Import MetaCoq.Template.All.
Require Import utilities.
Require Import definitions.
Require Import expand.
Require Import List.
Import ListNotations.
Require Import String.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 rec recursive_arg (f: constr) : int :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Fix recargs nbindu _ _ => Array.get recargs nbindu
  | Constr.Unsafe.Lambda _ body => Int.add 1 (recursive_arg body)
  | _ => 0
  end.

Ltac2 reduces_to_aux (f1 : constr) (f2: constr) :=
let f1' := (eval red in $f1) in
if Constr.equal f1' f2 then f1
else fail "not equal".

Ltac2 reduces_to (f1 : constr) (f2 : constr) :=
match Constr.Unsafe.kind f1 with
  | Constr.Unsafe.App f args => 
      if Constr.is_const f then reduces_to_aux f1 f2
      else 
        match Constr.Unsafe.kind f with
          | Constr.Unsafe.Var id => let f1' := Control.hyp id in reduces_to_aux f1' f2
          | _ => fail "not an applied constant or an applied variable"
        end
  | Constr.Unsafe.Constant _ _ => reduces_to_aux f1 f2
  | Constr.Unsafe.Var id => let f1' := Control.hyp id in reduces_to_aux f1' f2
  | _ => fail "not a constant"
end.

(* Looks for a constant in the goal 
or in the hypotheses which reduces to f, 
pose a local def if it fails to find one *)

Ltac2 rec find_term_reduces_to_in_goal (f : constr) (id : ident) :=
match! goal with
  | [ |- context [?t]] => reduces_to t f  
  | [ _ : context [?t] |- _ ] => reduces_to t f
  | [h : _ |-  _] => Message.print (Message.of_ident h); let f1 := Control.hyp h
     in Message.print (Message.of_ident h); reduces_to f1 f
  | [ |- _ ] => Std.pose (Some id) f ; find_term_reduces_to_in_goal f id
end.

Ltac2 id_or_fail (id : ident option) : ident :=
match id with
| None => fail "no ident given"
| Some id' => id'
end.

Ltac2 print_subterms h := 
  match! h with
  | context [ ?t ]  => Message.print (Message.of_constr t)
  | _ => fail "foo"
  end.

Ltac2 rec find_applied (u : unit) :=
  match! goal with
  | [ |- forall _ : _, _ ] => intros ; find_applied ()
  | [ |- context c [ ?t ]]  => 
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App f args => 
                if Constr.is_fix f then 
                (let recarg := recursive_arg f in
                  if Int.le recarg (Array.length args)
                  then 
                    let const := 
                    find_term_reduces_to_in_goal f (id_or_fail (Ident.of_string "new_fix")) in 
                    let inst := Pattern.instantiate c (Constr.Unsafe.make (Constr.Unsafe.App const args))
                    in print (of_constr inst)
                  else fail "not applied enough")
                else fail "not a fixpoint"
      | _ => fail "not an application"
      end
  end. 

Goal False.
Proof. ltac1:(get_def Datatypes.length; expand_hyp length_def).
ltac1:(let T := type of H in assert (H1 : False -> T) ; [
intro HFalse | ..]). find_applied ().




destruct l0 ; cbv fix ; fold (@Datatypes.length A0)

 |..]).

 let h := Control.hyp @H in
let t := Constr.type h in
 find_applied t.


print_subterms '(fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end).

 ltac1:(get_def length; expand_hyp length_def).
let h' := Control.hyp @H in 
let t := (Constr.type h') in 
let x:= find_applied t in Message.print (Message.of_constr x).

(* remove the nth last elements of a list *)
Fixpoint rem_last_elem {A} (n : nat) (l : list A) := match l, n with 
| nil, _ => nil
| cons _ _, 0 => l
| cons x xs, S n' => rem_last_elem n' xs
end.


Definition find_args (t1 t2 : term) := 
match t2 with
| tApp v l => 
    let n:= Datatypes.length l in 
    match t1 with 
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

Ltac eliminate_fix_cont H := fun k =>
first [
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
by (repeat (let x := fresh in intro x ; try (destruct x ; auto))) ; k H' ; clear H| k H].

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

Goal False.
get_def @Datatypes.length.
get_def Nat.add.
expand_hyp add_def.
eliminate_fix_cont H ltac:(fun H0 => let t := type of H0 in idtac).
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



