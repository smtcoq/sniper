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

Require Import utilities.
Require Import definitions.
From elpi Require Import elpi.
Require Import List.
Import ListNotations.

Ltac intros_destructn n := 
lazymatch n with
| 0 => let x := fresh in intro x; destruct x
| S ?n' => let H := fresh in intro H; intros_destructn n'
end.

(* TODO : best rewriting to handle other situations. 
The problem is the automatic conversion made by setoid rewrite *)
 
Ltac myrewrite Ty := 
repeat match goal with
| H1 : ?Ty1 |- _ => 
  constr_eq Ty Ty1 ;
  match goal with
    | H2 : ?T |- _ => setoid_rewrite H2 in H1 at 2 ; clear H2
    end
end.


Ltac mypose x := pose x.

Goal (forall (A : Type) (B : Type) (l : list A) (l' : list B), l = l).
intros_destructn 3. Abort.

Ltac myassert x n := 
let x' := eval cbv beta in x in
assert x' by (intros_destructn n ; reflexivity).

Elpi Tactic eliminate_fix_hyp.
Elpi Accumulate File "elpi/eliminate_fix.elpi".
Elpi Accumulate File "elpi/subterms.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate lp:{{

  pred gen_eqs i: list term, i: list term, o: list (pair term int).
    gen_eqs [F|L] Glob [pr R I|RS] :- !, 
      index_struct_argument F I,
      std.filter Glob (x\ const_reduces_to x F) L', 
      std.last L' Def, 
      subst_anon_fix F Def F', 
      mkEq F F' R, gen_eqs L Glob RS.
    gen_eqs [] _ [].

    pred assert_list_rewrite i: term, i: list (pair term int), i: goal, o: list sealed-goal.
    assert_list_rewrite H [pr Hyp I | XS] G GL :-
      int_to_term I I', coq.say I', coq.say {coq.term->string Hyp},
      coq.ltac.call "myassert" [trm Hyp, trm I'] G [G1 | _],
      coq.ltac.open (coq.ltac.call "myrewrite" [trm H]) G1 [G2 | _],
      coq.ltac.open (assert_list_rewrite H XS) G2 GL.
      assert_list_rewrite _H [] _G _GL.


  solve ((goal Ctx _ _ _ [trm H]) as G) GL :-
    globals_const_in_goal Ctx Glob, !, coq.say Glob,
    coq.typecheck H TyH ok,
    subterms_fix TyH L, !, coq.say L,
    gen_eqs L Glob R,
    assert_list_rewrite TyH R G GL.

}}.

Elpi Typecheck.

Section test.

Variable toto : nat -> nat.

Goal False -> False. intros. 
assert (H0 : (forall (A : Type) (l : list A), 
length l = (fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l)) by reflexivity. elpi eliminate_fix_hyp (H0).
assert (H1 : (forall (A : Type) (l : list A), 
length l = (fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l) -> False -> True) by (intros H1 HFalse; destruct HFalse).
elpi eliminate_fix_hyp (H1).
assert (H2 : forall n m, toto (Nat.add n m) =
(fix add (n m : nat) :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) n m) by admit.
elpi eliminate_fix_hyp (H2).
Abort. 

End test.

Tactic Notation "eliminate_fix_cont" constr(H) ltac(k) :=
elpi eliminate_fix_hyp H ; k H.

Tactic Notation "eliminate_fix_hyp" constr(H) :=
elpi eliminate_fix_hyp H.
