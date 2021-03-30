Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import BinInt.
Require Import Coq.Arith.PeanoNat.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.All.
Require Import List.
Import ListNotations.


(* Check is a MetaCoq term is a sort which is not Prop *)
Definition is_type (t : term) := match t with
                                 | tSort s => negb (Universe.is_prop s)
                                 |_ => false
                                  end.

(* This tactic checks if a hypothesis is already in the context *)
Ltac notHyp T  :=
repeat match goal with
  | [H : _ |- _] => let U := type of H in constr_eq U T ; fail 2
end.

(* A tactic version of if/else *)
Ltac if_else_ltac tac1 tac2 b := lazymatch b with
  | true => tac1
  | false => tac2
end.

(* Instanciate a hypothesis with the parameter x *)
Ltac instanciate H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => tryif (let H':= fresh H "_" x in pose (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x)) then idtac else (let H':= fresh H in pose (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x))
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

Ltac instanciate_type_ident H := 
let l := nil in
let P := type of H  in let P':= type of P in constr_eq P' Prop ; 
lazymatch P with
    | forall (x : ?A), _ =>
      let A' := eval hnf in A in 
is_type_quote A' ; repeat match goal with 
          |- context C[?y] => let Y := type of y in let Y' := eval hnf in 
Y in is_type_quote Y' ; let ident := instanciate_ident H y in constr:(ident :: l)
          end
end.


Goal ((forall (A: Type) (x : A), x=x) -> (forall (x : nat), x =x)).
Proof. intro H.
 let y := instanciate_ident H nat in idtac y.
 instanciate_type_ident H.
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



Ltac specialize_context := repeat specialize_context_aux ; repeat eliminate_id.


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

Ltac inst t := 
specialize_context ; instanciate_type_tuple t.

(* This is a trick to admit no parameter in the tactic inst :
 we instanciate with a trivial hypothesis and then 
we delete it *)

Tactic Notation "inst_no_parameter" := let H := fresh in 
assert (H : forall (x: Type), True) by (intros x ; exact I) ; inst H ; clear H ; match goal with 
| U : True |- _ => clear U
end.

(* Ltac return_id := fun k => let x := fresh "test" in k ; x. *)


Ltac return_id k :=
  let x := fresh "test" in
  let _ := match goal with _ => k end in
  x.


Goal False.

let y := return_id idtac in assert (y : True).
let y := return_id idtac in assert (y : True).
Abort.


(* TODO : Handle a list of identifiers ? *)


