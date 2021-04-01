Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.


Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).

Definition test x := match x with
| 0 => max 0 1
| S x => max 0 x
end.

(* Recursive, be careful: it can unfold definitions that we want to keep folded *)
Ltac get_definitions := repeat match goal with 
| |- context C[?x] =>
let x' := eval unfold x in x in (match goal with 
| _ : x = x' |- _ => fail 1
| _ => idtac
end ;
 assert (x = x') by (unfold x ; reflexivity))
| _ : context C[?x] |- _ => let x' := eval unfold x in x in (match goal with 
                  | _ : x = x' |- _ => fail 1
                  | _ => idtac
end ;
 assert (x = x') by (unfold x ; reflexivity))
end.

(* The basic tactic, not recursive *)
Ltac get_def x := 
let x' := eval unfold x in x in 
let H := fresh x "_def" in assert (H : x = x') by reflexivity.

Ltac get_def_cont x := 
let H := fresh  x "_def" in
let _ := match goal with _ => 
let x' := eval unfold x in x in assert (H : x = x') by reflexivity end in H.


Ltac unfold_recursive x := let x' := eval unfold x in x in try unfold_recursive x' ; 
(match goal with 
| H : x = x' |- _ => fail 1
| _ => idtac
end ; let H := fresh in
 assert (H : x = x') by (unfold x ; reflexivity)).

Ltac subst_def_no_clear x := repeat match goal with
| H : x = ?x', H' : ?x' = ?x''|- _ => rewrite H' in H ; subst_def_no_clear x''
end.


Ltac subst_def x := repeat match goal with
| H : x = ?x', H' : ?x' = ?x''|- _ => rewrite H' in H ; clear H' ; subst_def x''
end.

Ltac unfold_recursive_subst x := 
unfold_recursive x ; subst_def x.

(* MetaCoq version of the same tactic *)

Ltac unquote_env_aux e := match e with 
| [] => idtac
| ?x :: ?xs => unquote_term x ; unquote_env_aux xs
end.

(* Nothing about inductives for now *)
Fixpoint get_decl (e : global_env) := match e with 
| [] => []
| x :: e' => match (snd x) with
      | ConstantDecl u => match u.(cst_body) with
            | Some v => v :: get_decl e'
            | None => get_decl e'
            end
      | InductiveDecl u => get_decl e'
      end
end.

Ltac unquote_env e := let e' := constr:(fst e) in 
let l := constr:(get_decl e') in let l':= eval compute in l in 
unquote_env_aux l'.

Ltac rec_quote_term t idn := (run_template_program (tmQuoteRec t) ltac:(fun x => (pose  x as idn))).

Ltac get_definition_standard_library t := let e := fresh in rec_quote_term t e ;
unquote_env e ; clear e.









