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
From elpi Require Import elpi.
Require Import reflexivity.
Require Import unfold_reflexivity.
Require Import unfold_in.
Require Import expand.
Require Import List.
Import ListNotations.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

From Sniper.elpi Extra Dependency "eliminate_fix.elpi" as elimfix.
From Sniper.elpi Extra Dependency "subterms.elpi" as subs.
From Sniper.elpi Extra Dependency "utilities.elpi" as utils.

Ltac assert2 H2 Ty :=
  let H3 := fresh in 
  assert (H3 : Ty) by (intros; rewrite <- H2 ; auto).

Elpi Tactic setoid_rewrite_at2.
Elpi Accumulate File elimfix subs utils.


Elpi Accumulate lp:{{

  solve ((goal _ _ _ _ [trm H1, trm H2]) as G) GL :- std.do! [
     coq.typecheck H1 Ty1 ok,
     coq.typecheck H2 Ty2 ok,
     setoid_rewrite Ty1 Ty2 Ty3, 
     coq.ltac.call "assert2" [trm H2, trm Ty3] G GL, !].
  solve _ _ :- coq.ltac.fail 0 _.


}}.

Elpi Typecheck.

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
intros. ltac2:(let x := specialize_list 'H ['nat; 'Type]
in ()). Abort.

Ltac2 rec find_bounded_args (t : constr) (i : int) :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod bind t' => find_bounded_args t' (Int.add i 1)
| Constr.Unsafe.App u args => if Constr.equal u '(@eq) then 
  find_bounded_args (Array.get args 0) i
  else (drop_nlast (Array.to_list args) i)
| _ => fail "not an applied function"
end.
  

Ltac2 specialize_in_eq (h1 : constr) (h2 : constr) :=
let t := Constr.type h1 in
let t' := (eval cbv delta in $t) in
let args := find_bounded_args t' 0 in
let y := specialize_list h2 args in ().

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
  match Constr.Unsafe.kind t with
    | Constr.Unsafe.App t' a => 
      if Constr.equal t' '(@eq) then 
      let c := Array.get a 1 in 
      let rec aux c := 
        match Constr.Unsafe.kind c with
          | Constr.Unsafe.App u l => aux u
          | Constr.Unsafe.Fix tab k bda cstr => 
              let binder_fix := Array.get bda k in 
              let name := Option.get (Constr.Binder.name binder_fix) in
              let csts := Env.expand [name] in 
              let constantref := List.hd csts in
              let cst := Env.instantiate constantref in
              let cst' := Ltac1.of_constr cst in 
              let h' := Ltac1.of_constr h in
              ltac1:(x y |- fold x in y) cst' h'        
          | _ => ()
        end in aux c
      else ()
    | _ => ()
  end. 

Ltac2 rec fold_in_eq_aux2 (t : constr) (h : constr) :=
  match Constr.Unsafe.kind t with
    | Constr.Unsafe.Prod b t' => fold_in_eq_aux2 t' h
    | _ => fold_in_eq_aux1 t h
  end.

Ltac fold_in_eq H :=
  let T := type of H in
  let funct := ltac2:(t h |- 
  let t' := Ltac1.to_constr t in
    match t' with
      | Some t'' => 
        let h' := Ltac1.to_constr h in
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
  constr_eq Ty Ty1 ;
  lazymatch goal with
    | H2 : ?T |- _ => first [first [first [setoid_rewrite H2 in H1 at 2 ; clear H2
| specialize_in_eq H1 H2 ; setoid_rewrite H2 in H1 ; clear H2 | setoid_rewrite_at2 H1 H2 ]] | fold_in_eq H2; clear H1 ]
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
      std.rev Ctx Ctx',
      elim_pos_ctx Ctx' H H', (coq.ltac.call "myrewrite" [trm H']) G GS.

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
      coq.ltac.open (elim_pos_ctx_rewrite H) G1 [G2 | _GS'],
      coq.ltac.open (assert_list_rewrite H XS) G2 GL.
      assert_list_rewrite _H [] _G _GL.


  solve ((goal Ctx _ _ _ [trm H]) as G) GL :-
    globals_const_or_def_in_goal Ctx Glob,
    std.filter Glob is_fix Glob0,
    std.rev Ctx Ctx',
    std.map Glob0 (x\ add_pos_ctx Ctx' x) Glob',
    coq.typecheck H TyH ok,
    subterms_fix TyH L, !,
    std.map L (x\ add_pos_ctx Ctx' x) L',
    gen_eqs Ctx L' Glob' R,
    add_pos_ctx Ctx' TyH TyH',
    assert_list_rewrite TyH' R G GL.

}}.

Elpi Typecheck.

Tactic Notation "eliminate_fix_hyp'" constr(H) :=
elpi eliminate_fix_hyp (H).

Ltac eliminate_fix_hyp H := eliminate_fix_hyp' H.

Ltac eliminate_fix_cont H k :=
eliminate_fix_hyp H ; k H.

Section test_search.

Variable (A: Type).
Variable (CompDec : Type -> Type).
Variable (H : CompDec A).
Variable (eqb_of_compdec : forall (A : Type), CompDec A -> A -> A -> bool).

Fixpoint search (x : A) l :=
  match l with
  | [] => false
  | x0 :: l0 => orb (eqb_of_compdec A H x x0) (search x l0)
  end.

Goal forall (H0 : (search =
         (fix search (x : A) (l : list A) {struct l} : bool :=
            match l with
            | [] => false
            | x0 :: l0 => orb (eqb_of_compdec A H x x0) (search x l0)
            end))), False.
intros. eliminate_fix_hyp H0. Abort. 

End test_search.

Section test_ho.


Variable (A B: Type).
Variable (f: A -> B).

Goal False.
pose (map' := List.map f).
assert_refl map'.
unfold_refl H.
expand_hyp H.
unfold_refl H0.
unfold_in H0 map.
eliminate_fix_hyp H0.
Abort.

End test_ho.

Section test.

(* test bound variables in the context *)
Goal (Type -> False).
intro C.
assert (H : forall l, (length l) = (fix length (l : list C) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l) by reflexivity. eliminate_fix_hyp H.
Abort.

Goal (forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l).
intros.
pose (f1 := map g).
assert (H0 : forall l, f1 l =
     (fix map (l : list B) : list C :=
        match l with
        | nil => nil
        | a :: t => g a :: map t
        end) l) by reflexivity.
eliminate_fix_hyp H0.
Abort. 

Variable toto : nat -> nat.

Goal False -> False. intros. 
assert (H0 : (forall (A : Type) (l : list A), 
length l = (fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l)) by reflexivity. eliminate_fix_hyp H0.
assert (H1 : (forall (A : Type) (l : list A), 
length l = (fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l) -> False -> True) by (intros H1 HFalse; destruct HFalse).
eliminate_fix_hyp H1.
assert (H2' : forall n m, toto (Nat.add n m) =
(fix add (n m : nat) :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) n m) by admit.
eliminate_fix_cont H2' ltac:(fun H => idtac).
assert (H3' : forall A l, toto (length l) = toto ((fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l) -> True) by admit. eliminate_fix_hyp H3'.
Abort.

(* Test higher-order + polymorphism *) 

Fixpoint zip {A B : Type} (l : list A) (l' : list B) :=
  match l, l' with
  | [], _ => []
  | x :: xs, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys 
  end.

Goal (forall (A B C : Type)(f : A -> B) (g : A -> C) (l : list A),
map (fun (x : A) => (f x, g x)) l = zip (map f l) (map g l)).
intros A B C f g l.
pose (f0 := fun x : A => (f x, g x)).
pose (f1 := map f0).
assert (H : forall l : list A,
    f1 l =
    (fix map (l0 : list A) : list (B * C) :=
       match l0 with
       | [] => []
       | a :: t => f0 a :: map t
       end) l) by reflexivity.
eliminate_fix_hyp H.
assert (foo : forall l : list A,
    f1 l = match l with
           | [] => []
           | a :: t => f0 a :: map f0 t
           end) by assumption.
Abort.

End test.

Section debug_monomorphism.

Variable A B C : Type.

Goal (forall (f : A -> B) (g : A -> C) (l : list A),
map (fun (x : A) => (f x, g x)) l = zip (map f l) (map g l)).
intros f g l.
pose (f0 := fun x : A => (f x, g x)).
pose (f1 := map f0).
pose (f2 := map f).
pose (f3 := map (@id nat)).
assert (H : forall l : list nat,
    f3 l =
    (fix map (l0 : list nat) : list nat :=
       match l0 with
       | [] => []
       | a :: t => id a :: map t
       end) l) by reflexivity.
eliminate_fix_hyp H.
assert (H1' : forall l : list A,
    f2 l =
    (fix map (l0 : list A) : list B :=
       match l0 with
       | [] => []
       | a :: t => f a :: map t
       end) l) by reflexivity.
eliminate_fix_hyp H1'.
assert (H2 : forall l : list A,
    f1 l =
    (fix map (l0 : list A) : list (B * C) :=
       match l0 with
       | [] => []
       | a :: t => f0 a :: map t
       end) l) by reflexivity.
eliminate_fix_hyp H2. 
unfold f0 in f1.
assert (H3 : forall l : list A,
    f1 l =
    (fix map (l0 : list A) : list (B * C) :=
       match l0 with
       | [] => []
       | a :: t => (f a, g a) :: map t
       end) l) by reflexivity.
eliminate_fix_hyp H3.
assert (bar : forall l : list A, f2 l = match l with
                               | [] => []
                               | a :: t => f a :: map f t
                               end) 
by assumption.
assert (foo : forall l : list A,
    f1 l = match l with
           | [] => []
           | a :: t => f0 a :: map f0 t
           end) by assumption.
Abort.

End debug_monomorphism.



