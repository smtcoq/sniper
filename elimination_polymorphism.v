Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

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
  | _ => idtac "did not work"
      end.



(* Instanciate a hypothesis with the parameter x and return its identifier *)
Ltac instanciate_ident H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => let H':= fresh H in 
let _ := match goal with _ => pose (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x) end in H'
  | _ => idtac "did not work"
      end.






(* Reifies a term and calls is_type *)
Ltac is_type_quote t := let t' := eval hnf in t in
quote_term t' ltac:(fun T => if_else_ltac idtac fail ltac:(eval compute in (is_type T))).

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
| ?x => instanciate_type x
| ?y => fail 100 "Wrong parameter" y
end.

Ltac instanciate_type_tuple_all t := match t with
| pair ?a ?b => instanciate_type_all b ; instanciate_type_tuple_all a 
| ?x => instanciate_type_all x
| ?y => fail 100 "Wrong parameter" y
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
Proof. intros H. inst_clear app_length.
Abort.

Goal False -> forall (x : nat) (y : bool), x=x /\ y= y.
inst pair_equal_spec. clear pair_equal_spec_nat.
inst_clear_all pair_equal_spec.
Abort.
