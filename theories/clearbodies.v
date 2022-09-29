From MetaCoq Require Import All. 
Require Import String.
Open Scope string_scope.
From elpi Require Import elpi.

Require Import List.
Import ListNotations.

Ltac myclearbody x := clearbody x.

Elpi Tactic clearbody_list_tVar.
Elpi Accumulate lp:{{

  pred unwrap_ident i: term, o: term.
    unwrap_ident (app [{{tVar}}, ID]) ID.
    unwrap_ident _ _.

  pred unwrap_idents i: term, o: list term.
    unwrap_idents (app [{{@cons }}, _ , X, X'])  [ID|IDS] :- unwrap_ident X ID, unwrap_idents X' IDS.
    unwrap_idents (app [{{@nil}} | _])  [].
    unwrap_idents _ [].

  pred clearbody_metacoq i: list term, i: goal, o: list (sealed-goal).
    clearbody_metacoq [Str | Strs] ((goal Ctx _ _ _ _) as G) GL :- coq.term->string Str SQ,  rex.split "\"" SQ [S], 
    (std.mem Ctx (def X N _ _), coq.name->id N S), coq.ltac.call "myclearbody" [trm X] G [G'|_GL1], 
    coq.ltac.open (clearbody_metacoq Strs) G' GL.
    clearbody_metacoq [] _G _GL.
  
  solve (goal _ _ _ _ [trm L] as G) GL :-
    unwrap_idents L Strs, clearbody_metacoq Strs G GL.

}}.
Elpi Typecheck.

Tactic Notation "clearbody_list_tVar" constr(l) := elpi clearbody_list_tVar (l).

Lemma test2 : forall (n : nat) (b := n + 1) (r := b), nat.
Proof.
intros n b r.
clearbody_list_tVar [tVar "b"; tVar "r"].
exact b.
Qed.

