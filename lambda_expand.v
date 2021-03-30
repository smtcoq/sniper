Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.

(* A tactic version of if/else *)
Ltac if_else_ltac tac1 tac2 b := lazymatch b with
  | true => tac1
  | false => tac2
end.

Definition is_fun (t: term) :=
match t with 
| tLambda _ _ _ => true
| _ => false
end.

Definition get_type_of_lambda (t : term) := match t with 
| tLambda _ T _ => Some T
| _ => None
end.

MetaCoq Quote Definition unit_reif := unit.

Ltac rec_quote_term t idn := (run_template_program (tmQuoteRec t) ltac:(fun x => (pose  x as idn))).

Definition remove_option t := match t with 
| Some x => x 
| None => unit_reif 
end.


Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).

Ltac is_fun_quote t := 
quote_term t ltac:(fun t_reif => if_else_ltac idtac fail ltac:(eval compute in (is_fun t_reif))).



Ltac assert_type_lambda t := quote_term t
(fun t => let T := eval compute in (get_type_of_lambda t) in let T' :=
eval compute in (remove_option T) in run_template_program (tmUnquote T') 
ltac:(fun T => let T' := eval hnf in T.(my_projT2) in let H := fresh in assert (H : T'))).

Definition get_fun_applied (t : term) := 
match t with
| tLambda _ _ s => s
| _ => unit_reif
end.

MetaCoq Quote Definition eq_reif := Eval cbn in @eq.

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

Definition lifting_f f_reif T_entry T_return f_applied_reif := tProd 
{|binder_name := nAnon; binder_relevance := Relevant |} T_entry
(mkEq T_return (tApp f_reif [tRel 0]) f_applied_reif).

Ltac get_fun_applied_metacoq 
f_fold := let f:= eval unfold f_fold in f_fold in match type of f with 
| ?A -> ?B => quote_term A (fun A => quote_term B (fun B =>
quote_term f ltac:(fun f => let x:= eval compute in (get_fun_applied f) in quote_term f_fold 
ltac:(fun f_reif =>
let y := eval hnf in (lifting_f f_reif A B x) in run_template_program (tmUnquote y)
ltac:(fun y => let y' := eval hnf in y.(my_projT2) in 
let H := fresh in assert (H :y') by (simpl ; try reflexivity))))))
end.


Ltac get_fun_applied name := 
let H := fresh name "_def" in 
let T := type of name in match T with
| ?A -> ?B => 
assert (H : forall (x : A), name x = name x) ; try (reflexivity) ; unfold name at 2 in H
| _ => fail
end.


Definition get_fst_arg t := 
match t with
| tApp _ l => match l with 
              | nil => unit_reif
              | x :: xs => x
              end
| _ => unit_reif
end.

Definition get_snd_arg t := 
match t with
| tApp _ l => match l with 
              | [] | [ _ ]=> unit_reif
              | _ :: (y :: xs) => y
              end
| _ => unit_reif
end.

Definition get_thrd_arg t := 
match t with
| tApp _ l => match l with 
              | [] | [ _ ] | [_ ; _ ]=> unit_reif
              | _ :: (y :: ( z :: xs)) => z
              end
| _ => unit_reif
end.


Definition get_type_of_args t := 
let fix aux t (acc : list term) := match t with 
| tLambda _ ty s => aux s (ty::acc)
| _ => acc 
end in aux t [].


Fixpoint get_list_of_rel (i : nat) := match i with
| 0 => []
| S n => (get_list_of_rel n) ++ [tRel n]
end.


Fixpoint get_term_applied_aux (f f' : term) (acc : list term) 
 :=
(* the function reified f, acc is the type of each arguments *)
match f with 
| tLambda _ Ty s => ((get_term_applied_aux s f' (Ty :: acc)).1, 
(get_term_applied_aux s f' (Ty :: acc)).2)
| _ => let n := (List.length acc) in if Nat.eqb n 0 then (f', acc) else
 (tApp f' (get_list_of_rel (List.length acc)), acc)
end.


Definition get_term_applied (f : term) := get_term_applied_aux f f [].

Definition get_term_applied_eq (f : term) (ty : term) (t' : term)
 := mkEq ty (get_term_applied f).1 t'.

Fixpoint produce_eq_aux (f_fold : term) (f_unfold : term)
(type_of_args : list term) (codomain : term)  (n : nat) (n' : nat) := match type_of_args, n with
| [], 0 => get_term_applied_eq f_fold codomain (get_term_applied f_unfold).1
| x :: xs, S m  => tProd {| binder_name := nAnon; binder_relevance := Relevant |} x (produce_eq_aux
(tApp f_fold [tRel (n' - n)])
 f_unfold
xs codomain m n')
| _ , _ => unit_reif
end.

Definition produce_eq (f_fold : term) (f_unfold : term)
(type_of_args : list term) (codomain : term) := produce_eq_aux f_fold
f_unfold type_of_args codomain (Datatypes.length type_of_args) (Datatypes.length type_of_args).



Definition codomain_max t := 
let fix aux t default :=
match t with 
| tLambda _ x s => aux s x
| _ => default
end
in aux t unit_reif.



Ltac lambda_expand_all H := let t := type of H in 
quote_term t ltac:(fun t => 
let f_fold := eval cbv in (get_snd_arg t) 
in let f_unfold := eval cbv in (get_thrd_arg t) 
in let type_of_args := eval cbv in (get_type_of_args f_unfold) 
in let codomain := eval cbv in (codomain_max f_unfold) 
in let x := eval cbv in (produce_eq f_fold f_unfold type_of_args codomain)
in run_template_program (tmUnquote x) ltac:(fun z => 
let u := eval hnf in (z.(my_projT2)) 
in assert u by reflexivity)).









