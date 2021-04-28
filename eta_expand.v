Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import definitions.
Require Import Coq.Arith.PeanoNat.
Require Import String.



MetaCoq Quote Definition eq_reif := Eval cbn in @eq.

Ltac notHyp T  :=
repeat match goal with
  | [H : _ |- _] => let U := type of H in constr_eq U T ; fail 2
end.

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

Definition mkProd T u :=
tProd {| binder_name := nAnon; binder_relevance := Relevant |} T u.

Definition mkApp t u :=
tApp t [u].

Definition is_type_of_fun (T : term) :=
match T with
| tProd _ _ _ => true
| _ => false
end.

Definition list_of_args_and_codomain (t : term) := let fix aux acc t := match t with
| tProd _ t1 t2 => aux (t1 :: acc) t2
| _ => (acc, t)
end in aux [] t.

Fixpoint gen_eq (l : list term) (B : term) (t : term) (u : term) {struct l} := 
match l with
| [] => mkEq B t u
| A :: l' => mkProd A (gen_eq l' B (mkApp (lift 1 0 t) (tRel 0)) (mkApp (lift 1 0 u) (tRel 0)))
end.


Ltac eta_expand_hyp' H := 
lazymatch type of H with 
| @eq ?A ?t ?u => 
let H' := fresh in quote_term A ltac:(fun A =>
let b := eval cbv in (is_type_of_fun A) in 
match b with
| true =>
quote_term t ltac:(fun t =>
quote_term u ltac:(fun u =>
let p := eval cbv in (list_of_args_and_codomain A) in 
let l := eval cbv in (rev p.1) in 
let B := eval cbv in p.2 in 
let eq := eval cbv in (gen_eq l B t u)
in run_template_program (tmUnquote eq) 
ltac:(fun z => 
let u := eval hnf in (z.(my_projT2)) 
in assert (H': u) by (intros ; rewrite H; reflexivity) ; idtac A)))
| false => fail "not a higher-order equality"
end)
| _ => fail "not an equality"
end.

Ltac expand_hyp H := 
lazymatch type of H with 
| @eq ?A ?t ?u => 
let H' := fresh in quote_term A ltac:(fun A =>
quote_term t ltac:(fun t =>
quote_term u ltac:(fun u =>
let p := eval cbv in (list_of_args_and_codomain A) in 
let l := eval cbv in (rev p.1) in 
let B := eval cbv in p.2 in 
let eq := eval cbv in (gen_eq l B t u)
in run_template_program (tmUnquote eq) 
ltac:(fun z => 
let u := eval hnf in (z.(my_projT2)) 
in assert (H': u) by (intros ; rewrite H; reflexivity)))))
| _ => fail "not an equality" 
end.




Ltac expand_hyp_cont H := fun k =>
lazymatch type of H with 
| @eq ?A ?t ?u => quote_term A ltac:(fun A =>
quote_term t ltac:(fun t =>
quote_term u ltac:(fun u =>
let p := eval cbv in (list_of_args_and_codomain A) in 
let l := eval cbv in (rev p.1) in 
let B := eval cbv in p.2 in 
let eq := eval cbv in (gen_eq l B t u)
in run_template_program (tmUnquote eq) 
ltac:(fun z => 
let u := eval hnf in (z.(my_projT2)) in let H' := fresh in 
(assert (H': u) by (intros ; rewrite H; reflexivity) ; 
k H'))))) 
| _ => fail "not an equality"
end.

Ltac expand_tuple p := fun k => 
match constr:(p) with
| (?x, ?y) =>
expand_hyp_cont x ltac:(fun H' => expand_tuple constr:(y) ltac:(fun p => k (H', p))) ; clear x
| unit => k unit
end.

Goal False.
get_def length.
expand_hyp length_def.
assert (forall x : string, length x = match x with 
| ""%string => 0
| String _ s' => S (length s') 
end). intros x. destruct x ; simpl ; reflexivity.
Abort. 

Ltac expand_fun f :=
let H:= get_def_cont f in expand_hyp H ; clear H.

Goal False.
get_def length.
expand_hyp length_def.
expand_fun Datatypes.length.

Goal forall (A: Type) (l : list A) (a : A), hd a l = a -> tl l = [].
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => idtac H')).

Abort.

(* TODO : possible de clear ??? Truc vraiment bizarre avec des hypothèses qui changent
de nom dès qu'on ajoute clear x à la tactique expand_tuple *)
(* TODO : beta réduction
tApp (fun x => t(x)) y => subst ..., ne se fait pas automatiquement quand c'est des fixpoints
*)











