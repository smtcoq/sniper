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
Require Import BinInt.
Require Import Coq.Arith.PeanoNat.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.All.
Require Import List.
Require Import utilities.
Import ListNotations.


(* Instanciate a hypothesis with the parameter x *)
Ltac instanciate H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => tryif (let H':= fresh H "_" x in assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x)) then idtac else (let H':= fresh H in assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x))
  | _ => fail
      end.


(* Instanciate a hypothesis with the parameter x and return its identifier *)
Ltac instanciate_ident H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => let H':= fresh H in 
let _ := match goal with _ => assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x) end in H'
  | _ => fail
      end.


Goal (forall (A : Type) (B : Type), A = A /\ B = B) ->  forall (x : nat) (y : bool), x=x /\ y= y.
intro H.
let H' := instanciate_ident H bool in instanciate H' bool.
Abort.



(* Reifies a term and calls is_type *)
Ltac is_type_quote t := let t' := eval hnf in t in let T :=
metacoq_get_value (tmQuote t') in if_else_ltac idtac fail ltac:(eval compute in (is_type T)).


Ltac is_type_quote_bool t := let t' := eval hnf in t in let T :=
metacoq_get_value (tmQuote t') in constr:(is_type T).


Fixpoint list_of_subterms (t: term) : list term := match t with
| tLambda _ Ty u => t :: (list_of_subterms Ty) ++ (list_of_subterms u)
| tProd _ Ty u => t :: (list_of_subterms Ty) ++ (list_of_subterms u)
| tLetIn _ u v w => t :: (list_of_subterms u) ++ (list_of_subterms v) ++ (list_of_subterms w)
| tCast t1 _ t2 => t :: (list_of_subterms t1) ++ (list_of_subterms t2)
| tApp u l => t :: (list_of_subterms u) ++ (List.flat_map list_of_subterms l)
| tCase _ t1 t2 l => t:: (list_of_subterms t1) ++ (list_of_subterms t2) ++ 
(List.flat_map (fun x => list_of_subterms (snd x)) l)
| tFix l _  => t :: (List.flat_map (fun x => list_of_subterms (x.(dbody))) l)
| tCoFix l _ => t :: (List.flat_map (fun x => list_of_subterms (x.(dbody))) l)
| _ => [t]
end.


Definition filter_closed (l: list term) := List.filter (closedn 0) l.


Ltac get_list_of_closed_subterms t := let t_reif := metacoq_get_value (tmQuote t) in 
let l := eval cbv in (filter_closed (list_of_subterms t_reif)) in l. 


Ltac return_unquote_tuple_terms l := let rec aux l acc :=
match constr:(l) with
| nil => constr:(acc)
| cons ?x ?xs => 
  let y := metacoq_get_value (tmUnquote x) in 
  let u := constr:(y.(my_projT2)) in 
  let w := eval hnf in u in
  let T := type of w in 
  let b0 := ltac:(is_type_quote_bool T) in 
  let b := eval hnf in b0 in
    match b with 
    | true => (aux xs (pair w acc)) 
    | false => aux xs acc
    end
end
in aux l unit.

Ltac return_tuple_subterms_of_type_type := match goal with
|- ?x => let l0 := (get_list_of_closed_subterms x) in let l := eval cbv in l0 in return_unquote_tuple_terms l
end.


Goal forall (A: Type) (x:nat) (y: bool) (z : list A), y = y -> z=z -> x = x.
let t := return_tuple_subterms_of_type_type in pose t.
Abort.

Goal forall (A : Type) (l : list A), Datatypes.length l = 0 -> l = nil.
let t := return_tuple_subterms_of_type_type in pose t.
Abort.

Ltac instanciate_tuple_terms H t := match t with
| (?x, ?t') => try (let H' := instanciate_ident H x in let u := type of H' in
instanciate_tuple_terms H' t) ; try (instanciate_tuple_terms H t')
| unit =>  let T := type of H in
           match T with
            | forall (y : ?A), _ => constr_eq A Type ; clear H
            | _ => idtac
            end
end.

Ltac instanciate_tuple_terms_goal H := let t0 := return_tuple_subterms_of_type_type in 
let t := eval cbv in t0 in instanciate_tuple_terms H t.

Goal (forall (A B C : Type), B = B -> C = C -> A = A) -> nat = nat -> bool = bool.
intros H.
let p := return_tuple_subterms_of_type_type in pose p.
instanciate_tuple_terms_goal H.
Abort.


Ltac instanciate_tuple_terms_tuple_hyp t terms := match t with 
| (?H, ?t') => instanciate_tuple_terms H terms ; instanciate_tuple_terms_tuple_hyp t' terms
| unit => idtac
end.


Ltac instanciate_tuple_terms_tuple_hyp_no_unit t terms := lazymatch t with 
| (?t1, ?t2 ) => instanciate_tuple_terms_tuple_hyp_no_unit t1 terms ; 
instanciate_tuple_terms_tuple_hyp_no_unit t2 terms
| ?H => let T := type of H in 
     match T with 
  | forall (y : ?A), _ => constr_eq A Type ; try (instanciate_tuple_terms H terms)
  | _ => try (let U := type of T in constr_eq U Prop ; notHyp H ; let H0 := fresh H in assert (H0 : T) by exact H)
  end
end.

Ltac elimination_polymorphism t0 := 
let t := eval cbv in t0 in 
let terms0 := return_tuple_subterms_of_type_type in 
let terms := eval cbv in terms0 in 
let h0 := hyps in 
let h := eval cbv in h0 in
instanciate_tuple_terms_tuple_hyp_no_unit t terms ; 
instanciate_tuple_terms_tuple_hyp h terms.

Ltac test t0 := 
let t := eval cbv in t0 in 
let h0 := hyps in 
let h := eval cbv in h0 in
let x := constr:((nat, (bool, unit))) in 
instanciate_tuple_terms_tuple_hyp_no_unit t x ; 
instanciate_tuple_terms_tuple_hyp h x.

Ltac test2 t0 :=
let h0 := hyps in
let t := eval cbv in t0 in 
let x := constr:((nat, (bool, unit))) in
instanciate_tuple_terms_tuple_hyp_no_unit t0 x.


Goal (forall (A B C : Type), B = B -> C = C -> A = A) -> nat = nat -> bool = bool.
intro.
elimination_polymorphism (rev_involutive, unit).

Abort.


Tactic Notation "inst" := elimination_polymorphism unit.
Tactic Notation "inst" constr(t) := elimination_polymorphism (t, unit).


Goal (forall (A : Type) (a : A), a = a) -> (forall (x : nat), x = x).
Proof. intros H. inst app_length.

Abort.

Section test.

Variable A : Type. 
 Theorem nil_cons : forall (x:A) (l:list A), [] <> x :: l.
  Proof.
    intros. unfold "<>". intro H. inversion H.
  Qed.

Goal False -> forall (x : nat) (y : bool), x=x /\ y= y.
inst (pair_equal_spec, app_length, nil_cons, app_comm_cons).
Abort.


Goal True -> forall (x:A) (l:list A), [] <> x :: l.
intros.
test2 nil_cons. apply nil_cons0. Qed.

End test.
