Require Import Triggers.
Require Import Printer.
Require Import List.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
Import Unsafe.
From Ltac2 Require Import Message.
Import ListNotations.

Ltac2 initial_state () :=
  let hyps := Control.hyps () in
  let g := Control.goal () in
  (hyps, Some g).

Ltac2 initial_computed_subterms () :=
  { subterms_coq_goal := ([], None)}.

Ltac2 env_triggers () :=
  { env_triggers := [] }.

Ltac2 args_used () :=
  { args_used := [['unit]] }. (* arbitrary "already used argument" for tests only *)

Ltac2 test_trigger (t: trigger) :=
  let init := initial_state () in
  let env := env_triggers () in
  let initcomp := initial_computed_subterms () in
  let args := args_used () in
  let res := interpret_trigger init env args initcomp true t in
  print_interpreted_trigger res.
 
Ltac2 test_anon () :=
  TMetaLetIn (TContains (TSomeHyp, Arg Constr.type) (TLambda tDiscard tDiscard (Arg id))) ["H"; "f"]
  (TNot (TMetaLetIn (TContains (TNamed "H", NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
  (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg)))).

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
Fail test_trigger (TContains (TGoal, NotArg) (TFix (TAny (Arg id)) tDiscard NotArg)).
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



