From elpi Require Import elpi.
Require Import List.
Import ListNotations.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac intros_destructn n := 
lazymatch n with
| 0 => let x := fresh in intro x; destruct x
| S ?n' => let H := fresh in intro H; intros_destructn n'
end.

Ltac myrewrite Ty := 
repeat match goal with
| H1 : ?Ty1 |- _ => constr_eq Ty Ty1 ; idtac Ty1;
             match reverse goal with
             | H2 : ?T |- _ => idtac T; setoid_rewrite H2 in H1 ; clear H2
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
      int_to_term I I',
      coq.ltac.call "myassert" [trm Hyp, trm I'] G [G1 | _],
      coq.ltac.open (coq.ltac.call "myrewrite" [trm H]) G1 [G2 | _],
      coq.ltac.open (assert_list_rewrite H XS) G2 GL.
      assert_list_rewrite _H [] _G _GL.


  solve ((goal Ctx _ _ _ [trm H]) as G) GL :-
    globals_const_in_goal Ctx Glob, !, 
    coq.typecheck H TyH ok, 
    subterms_fix TyH L, !, 
    gen_eqs L Glob R,
    assert_list_rewrite TyH R G GL.

}}.

Elpi Typecheck. (*     %coq.typecheck H TyH ok, 
    %subterms_fix TyH L,*)


Print length.
Goal False -> False. intros. 
assert (H1 : forall n m, id (Nat.add n m) =
(fix add (n m : nat) :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) n m) by reflexivity.
elpi eliminate_fix_hyp (H1).
