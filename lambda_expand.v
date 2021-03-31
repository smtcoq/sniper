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
Unset Strict Unquote Universe Mode.


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
| tLambda _ Ty s => get_term_applied_aux s f' (Ty :: acc) 
| _ => let n := (List.length acc) in if Nat.eqb n 0 then (f', acc) else
 (tApp f' (rev (get_list_of_rel n)), acc)
end.


Definition get_term_applied (f : term) := get_term_applied_aux f f [].

Definition get_term_applied_eq (f : term) (ty : term) (t' : term)
 := mkEq ty (get_term_applied f).1 t'.

Fixpoint produce_eq_aux (f_fold : term) (f_unfold : term)
(type_of_args : list term) (codomain : term)  (n : nat) (n' : nat) := match type_of_args, n with
| [], 0 => get_term_applied_eq f_fold codomain (get_term_applied f_unfold).1
| x :: xs, S m  => tProd {| binder_name := nAnon; binder_relevance := Relevant |} x (produce_eq_aux
(tApp f_fold [tRel (n'-1)])
 f_unfold
xs codomain m (n'-1))
| _ , _ => unit_reif
end.

Definition produce_eq (f_fold : term) (f_unfold : term)
(type_of_args : list term) (codomain : term) := produce_eq_aux f_fold
f_unfold (rev type_of_args) codomain (Datatypes.length type_of_args) (Datatypes.length type_of_args).



Fixpoint codomain_max t := 
match t with 
| tProd _ x s => codomain_max s
| x => x
end.

MetaCoq Quote Definition type_reif := Type.

Fixpoint correction args := match args with
| [] => []
| x :: xs => match x with 
          | tSort s => type_reif :: correction xs
          | _ => x :: correction xs
end
end.

Ltac lambda_expand_all H := let t := type of H in 
quote_term t ltac:(fun t => 
let f_fold := eval cbv in (get_snd_arg t) 
in let f_unfold := eval cbv in (get_thrd_arg t) 
in let type_of_args := eval cbv in ((get_type_of_args f_unfold)) 
in let codomain := eval cbv in (codomain_max f_unfold) 
in let x := eval cbv in (produce_eq f_fold f_unfold type_of_args codomain)
in run_template_program (tmUnquote x) ltac:(fun z => 
let u := eval hnf in (z.(my_projT2)) 
in assert u by reflexivity)).

Ltac lambda_expand_fun f := let f_unfold := eval unfold f in f in 
let T := type of f in quote_term T (fun T_reif =>
quote_term f ltac:(fun f_fold =>
quote_term f_unfold ltac:(fun f_unfold =>
let type_of_args := eval cbv in (get_type_of_args f_unfold)
in let codomain := eval cbv in (codomain_max T_reif) 
in let x := eval cbv in (produce_eq f_fold f_unfold type_of_args codomain)
in run_template_program (tmUnquote x) ltac:(fun z => 
let u := eval hnf in (z.(my_projT2)) 
in assert u by reflexivity)))). 

Ltac lambda_expand_fun_test f := let f_unfold := eval unfold f in f in 
let T := type of f in quote_term T (fun T_reif =>
quote_term f ltac:(fun f_fold =>
quote_term f_unfold ltac:(fun f_unfold =>
let type_of_args := eval cbv in (get_type_of_args f_unfold)
in let codomain := eval cbv in (codomain_max T_reif) 
in let x := eval cbv in (produce_eq f_fold f_unfold type_of_args codomain)
in pose x
(* in run_template_program (tmUnquote x) ltac:(fun z => 
let u := eval hnf in (z.(my_projT2)) 
in assert u by reflexivity) *)))).


(* MetaCoq Quote Definition hd_unfold_reif := (fun (A : Type) (default : A) (l : list A) =>
      match l with
      | [] => default
      | x :: _ => x
      end).

MetaCoq Quote Definition typehd := (forall A : Type, A -> list A -> A).

Goal False.
unfold_recursive hd.
let codomain := eval cbv in (codomain_max typehd) in pose codomain.
Abort. 
Definition min1 (x : nat) := match x with
| 0 => 0
| S x => x
end.
Goal False.
lambda_expand_fun min1.
unfold_recursive hd.
lambda_expand_fun_test hd.
let x := constr:(tProd {| binder_name := nAnon; binder_relevance := Relevant |}
       (tSort
          {|
          Universe.t_set := {|
                            UnivExprSet.this := [(
                                              Level.Level
                                              "Coq.Lists.List.1", 0)];
                            UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                              (
                                              Level.Level
                                              "Coq.Lists.List.1", 0) |};
          Universe.t_ne := Logic.eq_refl |})
       (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
          (tRel 0)
          (tProd
             {| binder_name := nAnon; binder_relevance := Relevant |}
             (tApp
                (tInd
                   {|
                   inductive_mind := (MPfile
                                        ["Datatypes"%string;
                                        "Init"%string; "Coq"%string],
                                     "list"%string);
                   inductive_ind := 0 |} []) [tRel 1])
             (tApp
                (tInd
                   {|
                   inductive_mind := (MPfile
                                        ["Logic"%string; "Init"%string;
                                        "Coq"%string], "eq"%string);
                   inductive_ind := 0 |} [])
                [tRel 2;
                tApp
                  (tApp
                     (tApp
                        (tConst
                           (MPfile
                              ["List"%string; "Lists"%string;
                              "Coq"%string], "hd"%string) []) [
                        tRel 2]) [tRel 1]) [tRel 0];
                tApp
                  (tLambda
                     {|
                     binder_name := nNamed "A"%string;
                     binder_relevance := Relevant |}
                     (tSort
                        {|
                        Universe.t_set := {|
                                          UnivExprSet.this := [(
                                              Level.Level
                                              "Coq.Lists.List.1", 0)];
                                          UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                              (
                                              Level.Level
                                              "Coq.Lists.List.1", 0) |};
                        Universe.t_ne := Logic.eq_refl |})
                     (tLambda
                        {|
                        binder_name := nNamed "default"%string;
                        binder_relevance := Relevant |} 
                        (tRel 0)
                        (tLambda
                           {|
                           binder_name := nNamed "l"%string;
                           binder_relevance := Relevant |}
                           (tApp
                              (tInd
                                 {|
                                 inductive_mind := (
                                              MPfile
                                              ["Datatypes"%string;
                                              "Init"%string;
                                              "Coq"%string],
                                              "list"%string);
                                 inductive_ind := 0 |} []) [
                              tRel 1])
                           (tCase
                              ({|
                               inductive_mind := (
                                              MPfile
                                              ["Datatypes"%string;
                                              "Init"%string;
                                              "Coq"%string],
                                              "list"%string);
                               inductive_ind := 0 |}, 1, Relevant)
                              (tLambda
                                 {|
                                 binder_name := nNamed "l"%string;
                                 binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                       inductive_mind := (
                                              MPfile
                                              ["Datatypes"%string;
                                              "Init"%string;
                                              "Coq"%string],
                                              "list"%string);
                                       inductive_ind := 0 |} [])
                                    [tRel 2]) (tRel 3)) 
                              (tRel 0)
                              [(0, tRel 1);
                              (2,
                              tLambda
                                {|
                                binder_name := nNamed "x"%string;
                                binder_relevance := Relevant |}
                                (tRel 2)
                                (tLambda
                                   {|
                                   binder_name := nNamed "l0"%string;
                                   binder_relevance := Relevant |}
                                   (tApp
                                      (tInd
                                         {|
                                         inductive_mind := (
                                              MPfile
                                              ["Datatypes"%string;
                                              "Init"%string;
                                              "Coq"%string],
                                              "list"%string);
                                         inductive_ind := 0 |} [])
                                      [tRel 3]) 
                                   (tRel 1)))]))))
                  [tRel 2; tRel 1; tRel 0]])))) in pose x.

lambda_expand_fun hd. *)









