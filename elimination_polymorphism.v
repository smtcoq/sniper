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
  | forall (y : ?A), _ => tryif (let H':= fresh H "_" x in pose (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x)) then idtac else (let H':= fresh H in pose (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x))
  | _ => idtac "did not work"
      end.



(* Instanciate a hypothesis with the parameter x *)
Ltac instanciate_all H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => let H':= fresh H in pose (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x); try (instanciate_all H' x)
  | _ => fail
      end.



(* Instanciate a hypothesis with the parameter x and return its identifier *)
Ltac instanciate_ident H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => let H':= fresh H in 
let _ := match goal with _ => pose (H':= H) ; 
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

(* instanciates a polymorphic quantified hypothesis with all suitable subterms in the context *)
Ltac instanciate_type H := let P := type of H  in let P':= type of P in constr_eq P' Prop ; lazymatch P with
    | forall (x : ?A), _ =>
      let A' := eval hnf in A in 
is_type_quote A' ; repeat match goal with 
          |- context C[?y] => let Y := type of y in let Y' := eval hnf in 
Y in is_type_quote Y' ; instanciate H y
          end
end.

Ltac instanciate_type_all H := let P := type of H  in let P':= type of P in constr_eq P' Prop ; lazymatch P with
    | forall (x : ?A), _ =>
      let A' := eval hnf in A in 
is_type_quote A' ; repeat match goal with 
          |- context C[?y] => let Y := type of y in let Y' := eval hnf in 
Y in is_type_quote Y' ; instanciate_all H y
          end
end.


Ltac test t := 
      repeat match goal with
      |- context C[?y] => idtac y ; is_not_in_tuple constr:(t) y ; test (t, y)
end.

Ltac is_not_in_context x := 
repeat match goal with 
| y := x |- _ => fail 2
| _ => idtac
end.

Goal True.
pose (y := 1). Fail is_not_in_context 1. is_not_in_context 2.
exact I. Qed.

Print term.

Print fst.



Fixpoint list_of_subterms (t: term) : list term := match t with
| tLambda _ Ty u => t :: (list_of_subterms Ty) ++ (list_of_subterms u)
| tProd _ Ty u => t :: (list_of_subterms Ty) ++ (list_of_subterms u)
| tLetIn _ u v w => t :: (list_of_subterms u) ++ (list_of_subterms v) ++ (list_of_subterms w)
| tCast t1 _ t2 => t :: (list_of_subterms t1) ++ (list_of_subterms t2)
| tApp u l => t :: (list_of_subterms u) ++ (List.flat_map list_of_subterms l)
| tCase _ t1 t2 l => t:: (list_of_subterms t1) ++ (list_of_subterms t2) ++ 
(List.flat_map (fun x => list_of_subterms (snd x)) l)
| tFix _ _  => [t]
| tCoFix _ _ => [t]
| _ => [t]
end
(* with list_of_subterms_list (l : list term) : list term := match l with
| [] => nil
| x :: xs => list_of_subterms x ++ (list_of_subterms_list xs)
end *).

Print closedn.
Print filter.

Definition filter_closed (l: list term) := List.filter (closedn 0) l.


Ltac get_list_of_closed_subterms t := let t_reif := metacoq_get_value (tmQuote t) in 
let l := eval cbv in (filter_closed (list_of_subterms t_reif)) in l.

Require Import String.

Ltac instanciate_tuple t x := match t with
| (?H, ?t') => tryif (let H' := instanciate_ident H x in instanciate_tuple (H', t') x)
then idtac else (instanciate_tuple t' x)
| unit => idtac
end.

Ltac clear_tuple t := match t with
| (?H, ?t') => try (clear H) ; clear_tuple t'
| unit => idtac
end.

Ltac instanciate_tuple_terms_of_type_type h l := 
let rec aux l acc :=
match constr:(l) with
| nil => idtac
| cons ?x ?xs => let y := metacoq_get_value (tmUnquote x) in 
let u := constr:(y.(my_projT2)) in let w := eval hnf in u in 
tryif 
(let T := type of w in is_type_quote T ; instanciate_tuple h w) then aux xs (w, acc) else aux xs acc end
in aux l unit.

Ltac instanciate_all_hyps_with_reif l :=  repeat (let h := hyps in instanciate_tuple_terms_of_type_type h l).
(* TODO : écrire une tactique qui unquote une liste de terme clos et renvoie un tuple de termes Coq *) 

Goal (forall (A B C : Type), A = A /\ B = B /\ C=C) ->  forall (x : nat) (y : bool), x=x /\ y= y.
intros H.
let h := hyps in idtac h.
let l' := (get_list_of_closed_subterms (forall (x : nat) (y : bool), x = x /\ y = y))
in instanciate_all_hyps_with_reif l'.
Abort.




Goal forall (A: Type) (x:nat) (y: bool) (z : list A), y = y -> z=z -> x = x.                                                                                              
let u := get_subterms_in_goal tt in pose u.


Goal (forall (A B C : Type), B = B -> C = C -> A = A) -> nat = nat.
intros.
instanciate_all H nat. clear H0 H1 H2.
instanciate_type_all H.
Abort.





(* when a hypothesis is of type id Q, replaces it by Q *)
Ltac eliminate_id :=
  match goal with
    | H: ?P |- _ =>
      lazymatch P with
        | id ?Q => change P with Q in H
        | _ => fail
  end
end.

(* fold on a context with the tactic instanciate_type *)
Ltac specialize_context_aux :=
 match goal with
  | H: ?P |- _ => lazymatch P with 
                | id _ => fail 
                | _ => instanciate_type H ; change P with (id P) in H
             end
          end.

Ltac specialize_context_aux_all :=
 match goal with
  | H: ?P |- _ => lazymatch P with 
                | id _ => fail 
                | _ => instanciate_type_all H ; change P with (id P) in H
             end
          end.

Ltac specialize_context_aux_clear :=
 match goal with
  | H: ?P |- _ => lazymatch P with 
                | id _ => fail 
                | _ => instanciate_type H ; clear H
             end
          end.

Ltac specialize_context_aux_clear_all :=
 match goal with
  | H: ?P |- _ => lazymatch P with 
                | id _ => fail 
                | _ => instanciate_type_all H ; clear H
             end
          end.


Ltac specialize_context := repeat specialize_context_aux ; repeat eliminate_id.
Ltac specialize_context_all := repeat specialize_context_aux_all ; repeat eliminate_id.

Ltac specialize_context_clear := repeat specialize_context_aux_clear.
Ltac specialize_context_clear_all := repeat specialize_context_aux_clear_all.


(* A tactic to handle hypothesis in a list : the problem is that the user should hide the hypothesis 
in a let in definition in order to type the function *)

Ltac instanciate_type_list h := lazymatch h with
| nil => idtac 
| cons (let _ := ?hd in tt) ?h' => instanciate_type hd ; instanciate_type_list h'
end.

(* Another way to handle different hypothesis (more user-friendly) is to use tuples instead of lists *)

Ltac instanciate_type_tuple t := match t with
| pair ?a ?b => instanciate_type b ; instanciate_type_tuple a 
| ?x => try (instanciate_type x)
end.

Ltac instanciate_type_tuple_all t := match t with
| pair ?a ?b => try (instanciate_type_all b) ; instanciate_type_tuple_all a 
| ?x => try (instanciate_type_all x)
end.


Goal (forall (A : Type) (a : A), a = a) -> (forall (x : nat), x = x).
Proof. intros H. specialize_context_clear.
Abort.

Tactic Notation "inst" := specialize_context.
Tactic Notation "inst" constr(t) := specialize_context ; instanciate_type_tuple t.

Tactic Notation "inst_clear" := specialize_context_clear.
Tactic Notation "inst_clear" constr(t) := instanciate_type_tuple t ; specialize_context_clear.

Tactic Notation "inst_all" := specialize_context_all.
Tactic Notation "inst_all" constr(t) := specialize_context_all ; instanciate_type_tuple_all t.

Tactic Notation "inst_clear_all" := specialize_context_clear_all.
Tactic Notation "inst_clear_all" constr(t) := instanciate_type_tuple_all t ; specialize_context_clear_all.


Goal (forall (A : Type) (a : A), a = a) -> (forall (x : nat), x = x).
Proof. intros H. inst_clear_all False. inst_clear app_length.

Abort.

Goal False -> forall (x : nat) (y : bool), x=x /\ y= y.
inst pair_equal_spec. clear pair_equal_spec_nat.
inst_clear_all (pair_equal_spec, false, app_length).
Abort.
