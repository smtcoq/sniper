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

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

Definition mkProd T u :=
tProd {| binder_name := nAnon; binder_relevance := Relevant |} T u.

Definition mkApp t u :=
tApp t [u].

Definition list_of_args_and_codomain (t : term) := let fix aux acc t := match t with
| tProd _ t1 t2 => aux (t1 :: acc) t2
| _ => (acc, t)
end in aux [] t.

Fixpoint gen_eq (l : list term) (B : term) (t : term) (u : term) {struct l} := 
match l with
| [] => mkEq B t u
| A :: l' => mkProd A (gen_eq l' B (mkApp (lift 1 0 t) (tRel 0)) (mkApp (lift 1 0 u) (tRel 0)))
end.


Ltac eta_expand_hyp H := 
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
let u := eval hnf in (z.(my_projT2)) 
in assert u by (intros ; rewrite H; reflexivity)))))
| _ => fail "not an equality"
end.

Goal False.
get_def hd.
eta_expand_hyp hd_def.

Ltac expand_tuple p := 
match p with
| (?x, ?y) => let T := type of x in idtac x ; idtac y ; idtac T;
 eta_expand_hyp x ; idtac 2 ; clear x ; idtac 3 ; expand_tuple y ; idtac 4
| unit => idtac 5
| ?y => fail 100 "Wrong parameter" y
end.

Ltac expand_fun f :=
let H:= get_def_cont f in eta_expand_hyp H ; clear H.

Goal forall (A: Type) (l : list A) (a : A), hd a l = a -> tl l = [].

get_definitions_cont ltac:(fun p => expand_tuple p).
















