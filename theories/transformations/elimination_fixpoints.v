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

From Sniper Require Import utils.utilities.
From elpi Require Import elpi.
Require Import reflexivity.
Require Import unfold_reflexivity.
Require Import unfold_in.
Require Import expand.
From Stdlib Require Import List.
Import ListNotations.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
Set Default Proof Mode "Classic".

From Sniper.elpi Extra Dependency "eliminate_fix.elpi" as elimfix.
From Sniper.elpi Extra Dependency "subterms.elpi" as subs.
From Sniper.elpi Extra Dependency "utilities.elpi" as utils.

Ltac assert2 H2 Ty :=
  let H3 := fresh in 
  assert (H3 : Ty) by (intros; rewrite <- H2 ; auto).

Elpi Tactic setoid_rewrite_at2.
Elpi Accumulate File utils subs elimfix.


Elpi Accumulate lp:{{

  solve ((goal _ _ _ _ [trm H1, trm H2]) as G) GL :- std.do! [
     coq.typecheck H1 Ty1 ok,
     coq.typecheck H2 Ty2 ok,
     setoid_rewrite Ty1 Ty2 Ty3, 
     coq.ltac.call "assert2" [trm H2, trm Ty3] G GL, !].
  solve _ _ :- coq.ltac.fail 0 _.


}}.


Tactic Notation "setoid_rewrite_at2" constr(H1) constr(H2) :=
  elpi setoid_rewrite_at2 (H1) (H2) ; clear H2 ; clear H1.

Section test_rewrite.

Goal forall (f g h : forall (A B C : Type), A -> B -> C)
(H1 : forall A B C a b, f A B C a b = g A B C a b)
(H2 : forall A B C a b, g A B C a b = h A B C a b), False.
intros.
setoid_rewrite_at2 H1 H2. Abort.

End test_rewrite.


(* Quick patch : setoid_rewrite does not 
work with higher-order arguments, 
works only when the hypothesis we want to 
rewrite in is a toplevel equality 
with the constant on the left *)

Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 rec specialize_list (h : constr) (l : constr list) :=
match l with
| [] => h
| x :: xs => specialize ($h $x) ; specialize_list h xs
end.

Ltac2 rec drop_last (l : 'a list) :=
match l with
| [] => []
| x :: xs => x :: (match xs with [] => [] | _ :: _ => drop_last xs end)
end.

Ltac2 rec drop_nlast (l : 'a list) (i : int) :=
if Int.equal i 0 then []
else drop_nlast (drop_last l) (Int.sub i 1).

Goal ((forall (A B C : Type), C = C) -> False).
intros. ltac2:(let _ := specialize_list 'H ['nat; 'Type]
in ()). Abort.

Ltac2 rec find_bounded_args (t : constr) (i : int) :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod _ t' => find_bounded_args t' (Int.add i 1)
| Constr.Unsafe.App u args => if Constr.equal u '(@eq) then 
  find_bounded_args (Array.get args 0) i
  else (drop_nlast (Array.to_list args) i)
| _ => fail "not an applied function"
end.
  

Ltac2 specialize_in_eq (h1 : constr) (h2 : constr) :=
let t := Constr.type h1 in
let t' := (eval cbv delta in $t) in
let args := find_bounded_args t' 0 in
let _ := specialize_list h2 args in ().

Ltac specialize_in_eq x y :=
  let tac :=
  ltac2:(x y |-
    let x :=
      Option.get (Ltac1.to_constr x) in
    let y := 
      Option.get (Ltac1.to_constr y) in 
    specialize_in_eq x y) in tac x y.

Ltac intros_destructn n := 
 lazymatch n with
    | 0 => let x := fresh in intro x; destruct x
    | S ?n' => let H := fresh in intro H; intros_destructn n'
  end.

(* fold constants in equalities *)

Ltac2 fold_in_eq_aux1 (t : constr) (h : constr) :=
  printf "fold_in_eq_aux1 1";
  match Constr.Unsafe.kind t with
    | Constr.Unsafe.App t' a => 
      if Constr.equal t' '(@eq) then
      printf "fold_in_eq_aux1 2";
      let c := Array.get a 1 in 
      let rec aux c := 
        match Constr.Unsafe.kind c with
          | Constr.Unsafe.App u _ =>
              printf "fold_in_eq_aux1 3";
              aux u
          | Constr.Unsafe.Fix _ k bda _ =>
              printf "fold_in_eq_aux1 4";
              let binder_fix := Array.get bda k in
              printf "fold_in_eq_aux1 5";
              let name := Option.get (Constr.Binder.name binder_fix) in
              printf "fold_in_eq_aux1 6";
              let csts := Env.expand [name] in
              printf "fold_in_eq_aux1 7";
              printf "%i" (List.length csts);
              if Int.gt (List.length csts) 0 then (
                let constantref := List.hd csts in
                printf "fold_in_eq_aux1 8";
                let cst := Env.instantiate constantref in
                printf "fold_in_eq_aux1 9";
                let cst' := Ltac1.of_constr cst in
                printf "fold_in_eq_aux1 10";
                let h' := Ltac1.of_constr h in
                printf "fold_in_eq_aux1 11";
                ltac1:(x y |- fold x in y) cst' h') else ()
          | _ => ()
        end in aux c
      else ()
    | _ => ()
  end. 

Ltac2 rec fold_in_eq_aux2 (t : constr) (h : constr) :=
  match Constr.Unsafe.kind t with
    | Constr.Unsafe.Prod _ t' =>
      printf "fold_in_eq_aux2 1"; fold_in_eq_aux2 t' h;
      printf "fold_in_eq_aux2 2"
    | _ => fold_in_eq_aux1 t h
  end.

Ltac fold_in_eq H :=
  let T := type of H in
  let funct := ltac2:(t h |- 
  let t' := Ltac1.to_constr t in
    printf "fold_in_eq 1";
    match t' with
      | Some t'' => 
        let h' := Ltac1.to_constr h in
        printf "fold_in_eq 2";
        match h' with
          | Some h'' => fold_in_eq_aux2 t'' h''
          | None => ()
        end                
      | None => ()
    end) in funct T H.


(* TODO : best rewriting to handle other situations. 
The problem is the automatic conversion made by setoid rewrite *)
 
Ltac myrewrite Ty :=
repeat match goal with
| H1 : ?Ty1 |- _ =>
  idtac "===== Ty =====";
  idtac Ty;
  constr_eq Ty Ty1 ;
  idtac "===== Ty1 =====";
  idtac Ty1;
  idtac "===== H1 =====";
  idtac H1;
  lazymatch goal with
    | H2 : ?T |- _ =>
       idtac "===== T =====";
       idtac T;
       idtac "===== H2 =====";
       idtac H2;
       idtac "==========";
       first
         [ first
            [ first
              [ idtac ">>> HERE / 1"; setoid_rewrite H2 in H1 at 2 ; clear H2; idtac "<<< HERE / 1"
              | idtac ">>> HERE / 2"; specialize_in_eq H1 H2 ; setoid_rewrite H2 in H1 ; clear H2; idtac "<<< HERE / 2"
              | idtac ">>> HERE / 3"; setoid_rewrite_at2 H1 H2; idtac "<<< HERE / 3"
              ]
            ]
         | idtac ">>> HERE / 4"; fold_in_eq H2; clear H1; idtac "<<< HERE / 4" | idtac "HELLO" ]
    end
end.

Ltac mypose x := pose x.

Goal (forall (A : Type) (B : Type) (l : list A) (l' : list B), l = l).
intros_destructn 3. Abort.

Ltac myassert x n := 
let x' := eval cbv beta in x in
assert x' by (intros_destructn n ; reflexivity).

Elpi Tactic eliminate_fix_hyp.
Elpi Accumulate File elimfix.
Elpi Accumulate File subs.
Elpi Accumulate File utils.

(* TODO if / else elpi when L = [] to save some computation time *)
Elpi Accumulate lp:{{

  pred elim_pos_ctx_rewrite i: term, i: goal, o: list (sealed-goal).
  elim_pos_ctx_rewrite H ((goal Ctx _ _ _ _) as G) GS :-
    coq.say "HERE - rewrite - 1",
    std.rev Ctx Ctx',
    coq.say "HERE - rewrite - 2",
    elim_pos_ctx Ctx' H H',
    coq.say "HERE - rewrite - 3",
    (coq.ltac.call "myrewrite" [trm H']) G GS,
    coq.say "HERE - rewrite - 4".

  pred gen_eqs i: goal-ctx, i: list term, i: list term, o: list (pair term int).
  gen_eqs Ctx [F|L] Glob RS :- std.rev Ctx Ctx',
    elim_pos_ctx Ctx' F F',
    std.filter Glob (x\ elim_pos_ctx Ctx' x X', (coq.unify-leq X' F' ok ; abstract_unify X' F')) L',
    if (L' = []) (gen_eqs Ctx L Glob RS) fail.
  gen_eqs Ctx [F|L] Glob [pr R' I |RS] :- !, std.rev Ctx Ctx',
    elim_pos_ctx Ctx' F F',
    index_struct_argument F' I,
    std.filter Glob (x\ elim_pos_ctx Ctx' x X', (coq.unify-leq X' F' ok ; abstract_unify X' F')) L',
    std.last L' Def,
    elim_pos_ctx Ctx' Def Def',
    subst_anon_fix F' Def' F'',
    mkEq F' F'' R,
    add_pos_ctx Ctx' R R', gen_eqs Ctx L Glob RS.
  gen_eqs _ [] _ [].

  pred assert_list_rewrite i: term, i: list (pair term int), i: goal, o: list sealed-goal.
  assert_list_rewrite H [pr Hyp I | XS] ((goal Ctx _ _ _ _) as G) GL :-
    int_to_term I I',
    std.rev Ctx Ctx',
    elim_pos_ctx Ctx' Hyp Hyp',
    coq.ltac.call "myassert" [trm Hyp', trm I'] G [G1 | _GS],
    coq.say "HERE - >>> elim_pos_ctx_rewrite",
    coq.ltac.open (elim_pos_ctx_rewrite H) G1 [G2 | _GS'],
    coq.say "HERE - <<< elim_pos_ctx_rewrite",
    coq.ltac.open (assert_list_rewrite H XS) G2 GL.
  assert_list_rewrite _H [] _G _GL.


  solve ((goal Ctx _ _ _ [trm H]) as G) GL :-
    coq.say "HERE PLEASE",
    globals_const_or_def_in_goal Ctx Glob,
    coq.say "HERE 1",
    std.filter Glob is_fix Glob0,
    coq.say "HERE 2",
    std.rev Ctx Ctx',
    coq.say "HERE 3",
    std.map Glob0 (x\ add_pos_ctx Ctx' x) Glob',
    coq.say "HERE 4",
    coq.typecheck H TyH ok,
    coq.say "HERE 5",
    subterms_fix TyH L, !,
    coq.say "HERE 6",
    std.map L (x\ add_pos_ctx Ctx' x) L',
    coq.say "HERE 7",
    gen_eqs Ctx L' Glob' R,
    coq.say "HERE 8",
    add_pos_ctx Ctx' TyH TyH',
    coq.say "HERE - >>> assert_list_rewrite",
    assert_list_rewrite TyH' R G GL,
    coq.say "HERE - <<< assert_list_rewrite".
}}.


Tactic Notation "eliminate_fix_hyp'" constr(H) :=
elpi eliminate_fix_hyp (H).

Ltac eliminate_fix_hyp H := eliminate_fix_hyp' H.

Ltac eliminate_fix_cont H k :=
eliminate_fix_hyp H ; k H.

