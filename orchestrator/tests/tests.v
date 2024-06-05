Require Import orchestrator.triggers.
Require Import orchestrator.printer.
Require Import List.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Import Constr.
Import Unsafe.
From Ltac2 Require Import Message.
Import ListNotations.

Ltac2 env_triggers () :=
  { env_triggers := [] }.

Ltac2 init_already_triggered () :=
  { already_triggered := [] }.

Ltac2 init_interpretation_state () := 
  (* subterms already computed in the goal *)
  { subterms_coq_goal := ([], Some []);
  (* hypotheses or/and goal considered *)
    local_env := (Control.hyps (), Some (Control.goal ())) ; 
  (* are all the hypotheses considered ? *)
    global_flag := true;
  (* name of the tactic interpreted *)
    name_of_tac := "toto" }.

Ltac2 test_trigger (t: trigger) :=
  let env := env_triggers () in
  let alr_triggered :=  init_already_triggered () in
  let init := init_interpretation_state () in 
  let res := interpret_trigger init env alr_triggered t in
    match res with
      | Some x =>
          List.iter (fun x => print_interpreted_trigger (Some x)) x
      | None => printf "None" 
    end.
 
Ltac2 test_anon () :=
  TDisj (
  TMetaLetIn (TContains (TSomeHyp, Arg Constr.type) (TLambda tDiscard tDiscard (Arg id))) ["H"; "f"]
    (TConj (TNot (TMetaLetIn (TContains (TNamed "H", NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
    (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg))))
            (TIs (TNamed "f", Arg id) tDiscard)))
  (TMetaLetIn (TContains (TGoal, Arg id) (TLambda tDiscard tDiscard (Arg id))) ["H"; "f"]
  (TConj (TNot (TMetaLetIn (TContains (TNamed "H", NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
  (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg)))) (TIs (TNamed "f", Arg id) tDiscard))).

(* anonymous funs that are not branches of match *)

Lemma test u : match u with | 0 => True | S u => False end -> (fun x : nat => x) u = u  -> False.
intros H H1. test_trigger (test_anon ()). Abort.

Lemma test u : (fun x : nat => x) u = u -> False.
intros H. test_trigger (test_anon ()). Abort.

Lemma test u : match u with | 0 => True | S u => False end -> False.
intros H. test_trigger (test_anon ()). Abort.

(** Test De Brujin indexes, eq and anonymous functions **) 

Goal forall (n: nat), (fun x => x) n = n.
intros n.
test_trigger (TContains (TGoal , NotArg)  (TRel 1 NotArg)). 
test_trigger (TContains (TGoal, NotArg) (TLambda (TTerm 'nat (Arg id)) tDiscard NotArg)).
test_trigger (TContains (TGoal, NotArg) (TLambda tDiscard (TRel 1 NotArg) NotArg)). (* warning: as in 
the kernel, De Brujin indexes start with 1 *)
test_trigger (TIs (TGoal, NotArg) (TEq (TTerm 'nat (Arg id)) tDiscard tDiscard (Arg id))).
let g := Control.goal () in print_closed_subterms g.
Abort.

(** Test match, definitions and fixpoints **)

Goal (length =
fun A : Type =>
fix length (l : list A) : nat := match l with
                                 | [] => 0
                                 | _ :: l' => S (length l')
                                 end).
test_trigger (TContains (TGoal, NotArg) (TConstant None (Arg Constr.type))).
test_trigger (TContains (TGoal, NotArg) (TConstant (Some "length") (Arg Constr.type))).
test_trigger (TContains (TGoal, NotArg) (TFix tDiscard tDiscard NotArg)).
test_trigger (TContains (TGoal, NotArg) (TFix tDiscard tDiscard NotArg)).
test_trigger (TContains (TGoal, NotArg) (TCase tDiscard tDiscard (Some [TTerm '0 NotArg; tDiscard]) NotArg)).
Abort.

Goal  (forall A, @length A =
fix length (l : list A) : nat := match l with
                                 | [] => 0
                                 | _ :: l' => S (length l')
                                 end).
test_trigger (TContains (TGoal, NotArg) (TFix (TAny (Arg id)) tDiscard NotArg)).
test_trigger (TContains (TGoal, NotArg) (TFix tDiscard tDiscard NotArg)).
Abort.

(* Test named *)

Goal (forall (A B C : Prop), (A /\ B) -> (A /\ B) \/ C).
intros A B C H.
test_trigger (TIs (TGoal, NotArg) (TOr tDiscard tDiscard NotArg)).
test_trigger (TMetaLetIn (TIs (TGoal, NotArg) (TOr tArg tDiscard NotArg)) ["A"] (TIs ((TNamed "A"), NotArg) (TAnd tArg tDiscard NotArg))).
Abort.

Goal unit.
test_trigger (TIs (TGoal, NotArg) (TTerm 'unit (Arg id))). (* unit is in the list of used arguments *)
Abort.

Goal False.
ltac1:(pose proof app_nil_end).
test_trigger (TIs (TSomeHyp, NotArg) (TProd (TSort TBigType NotArg) tDiscard NotArg)).
Abort.

Ltac2 trigger_trakt_bool () :=
  TMetaLetIn (TIs (TSomeHyp, (Arg type)) (TType 'Prop NotArg)) ["H"]
  (TNot (TIs (TNamed "H", NotArg) (TEq (TTerm 'bool NotArg) tDiscard tDiscard NotArg))).

(* test for trakt tactic *)
Lemma toto (H : true = false) (H1 : andb true true = true) (n : nat) (H2 : False) : True.
Proof.
test_trigger (trigger_trakt_bool ()).
Abort.

Goal False.
ltac1:(pose proof app_nil_end).
test_trigger (trigger_trakt_bool ()).
Abort.

Fixpoint zip {A B : Type} (l : list A) (l' : list B) :=
  match l, l' with
  | [], _ => []
  | x :: xs, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys 
  end.

Ltac2 trigger_pattern_matching :=
  TContains (TSomeHyp, Arg id) (TCase tDiscard tDiscard None NotArg).

Goal (forall (H1 : forall (A B : Type) (l : list A) (l' : list B),
     zip l l' =
     match l with
     | [] => []
     | x :: xs => match l' with
                  | [] => []
                  | y :: ys => (x, y) :: zip xs ys
                  end end), False).
Proof. intros. test_trigger (trigger_pattern_matching). Abort.



