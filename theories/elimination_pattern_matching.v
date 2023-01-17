(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyfalse (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import MetaCoq.Template.All.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import String.
Require Import utilities.
Require Import definitions.
Require Import elimination_fixpoints.
Require Import expand.
Require Import List.
Import ListNotations.


Ltac create_evars_for_each_constructor i := 
let i_reif := metacoq_get_value (tmQuote i) in
match i_reif with
| tInd (?indu ?kn _) ?inst =>
let y := metacoq_get_value (tmQuoteInductive kn) in 
let n:= eval cbv in (get_nb_constructors_dcl y) in
let rec tac_rec u := match constr:(u) with 
      | 0 => idtac
      | S ?m => let H' := fresh in let H'_evar := fresh H' in epose (H' := ?[H'_evar] : Prop) ; tac_rec m
    end in tac_rec n
| _ => idtac 
end.

Goal True.
create_evars_for_each_constructor bool.
create_evars_for_each_constructor unit.
create_evars_for_each_constructor nat.
Abort.

Ltac intro_and_return_last_ident n := 
match constr:(n) with
| 0 => let u := fresh in let _ := match goal with _ => intro u end in u
| S ?m => let H := fresh in let _ := match goal with _ => intro H end in intro_and_return_last_ident m
end.

Ltac intro_and_tuple_rec n l := 
match constr:(n) with
| 0 => let u := fresh in let _ := match goal with _ => intro u end in constr:((u, l))
| S ?m => let H := fresh in let _ := match goal with _ => intro H end in intro_and_tuple_rec m (H, l)
end.

Ltac intro_and_tuple n :=
intro_and_tuple_rec n unit.

Ltac revert_tuple_clear p indu :=
lazymatch constr:(p) with
| (?x, ?y) => match indu with 
          | context [x] => clear x
          | _ => revert x
           end 
; revert_tuple_clear y indu
| unit => idtac
end.

Definition head_tuple (A B : Type) (x : A×B) := match x with
|(y, z) => y
end.

Definition tail_tuple (A B : Type) (x : A*B) := match x with
|(y, z) => z
end.

Ltac detect_var_match H :=

let T := type of H in 
let H' := fresh in 
assert (H' : False -> T) by
(match goal with | |-context C[match ?x with _ => _ end] => idtac end; let Hfalse := fresh in 
intro Hfalse; destruct Hfalse) ; clear H' ; idtac.

Ltac remove_app t :=
lazymatch constr:(t) with 
| ?u ?v => remove_app u 
| _ => t
end.

Goal forall (A : Type) (x: list A), x = x.
Proof. intros. let T := type of x in let T' := remove_app T in pose T'.
reflexivity.
Qed.

Ltac revert_count := 
let rec revert_count_rec n :=
match goal with
| H : _ |- _ => let _ := match goal with _ => revert H end in revert_count_rec (S n)
| _ => n
end in revert_count_rec 0.

Ltac is_a_variable x :=
let x':= metacoq_get_value (tmQuote x) in 
match x' with 
| tVar _ => idtac
| _ => fail
end.

Ltac contains t u :=
match t with
| context [u] => idtac
| _ => fail
end.

Ltac all_quantifers_introduced :=
lazymatch goal with
| |- forall _, _ => fail
| _ => idtac
end.

Ltac elim_match_with_no_forall H :=
  let U := type of H in 
  match U with 
| context C[match ?expr with _ => _ end] => 
    let Ty := type of expr in 
    let T' := remove_app Ty in 
    create_evars_for_each_constructor T' ;
    let foo := fresh in 
    assert (foo : False -> U) 
by (let Hfalse := fresh in
intro Hfalse ; tryif (is_a_variable expr)
then (case expr)
else (case_eq expr) ;
match goal with 
| u : Prop |- ?G => instantiate (u := G); destruct Hfalse
end) ; clear foo ; 
repeat match goal with 
| u : Prop |-_ => let H0 := fresh in let u' := eval unfold u in u in assert (H0 : u')  by 
(first [ try (rewrite H); reflexivity
|intros ; match goal with 
| Hinv : _ |- _ => rewrite Hinv in H ; auto
end]); try elim_match_with_no_forall H0 ; clear u 
end
end ; clear H.


Ltac eliminate_dependent_pattern_matching H :=
  let n := fresh "n" in 
  let T := fresh "T" in 
  epose (n := ?[n_evar] : nat) ;
  epose (T := ?[T_evar]) ;
  let U := type of H in
  let H' := fresh in
  assert (H' : False -> U);
  [ let HFalse := fresh in 
    intro HFalse; 
    let rec tac_rec m x :=
        match goal with
      | |- context C[match ?expr with _ => _ end] => match constr:(m) with
                                    | 0 => fail
                                    | S ?p => contains expr x ; instantiate (n_evar := p) ; 
                                              let Ty := type of expr in let T' := remove_app Ty in
                                              instantiate (T_evar := T') 
                                     end 
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y
      | _ => fail 
      end
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ; let indu := eval unfold T in T in 
create_evars_for_each_constructor indu ; let foo := fresh in assert 
(foo : False -> U) by 
(let Hfalse' := fresh in intro Hfalse' ; 
let nb_var := eval unfold n in n in
let t := intro_and_tuple nb_var in 
match goal with
|- context C[match ?expr with _ => _ end] => 
  let var_match := eval cbv in (head_tuple _ _ t) in
  let var_to_revert := eval cbv in (tail_tuple _ _ t) in
  tryif (constr_eq var_match expr)
then 
  (case var_match ; 
  let indu' := type of var_match in clear var_match ; 
  revert_tuple_clear var_to_revert indu')
else 
  (case_eq expr ; 
  let indu' := type of expr in revert var_match ;
  revert_tuple_clear var_to_revert indu')
 end 
  ; match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse' end)
; clear foo ; 
repeat match goal with 
| u : Prop |-_ => let H0 := fresh in let u' := eval unfold u in u in assert (H0 : u')  by 
(first 
[intros; try (rewrite H); reflexivity | first [
let foo := fresh in assert (foo := H) ; intros; rewrite foo ;
match goal with 
| Hinv : ?U |- context [match ?expr with _ => _ end] => let U' := type of
U in constr_eq U' Prop ; destruct expr; try intros ;
try inversion Hinv ;
 auto end |
repeat match goal with 
| |- forall x, _ => intro x ; try (specialize (H x)); try (rewrite x in H) ; try 
(inversion x) ; auto
| _ => idtac
end]]); clear u ; try (eliminate_dependent_pattern_matching H0) end] ; clear H ; 
clear n; clear T.

Tactic Notation "eliminate_dependent_pattern_matching" constr(H) :=
first [eliminate_dependent_pattern_matching H | elim_match_with_no_forall H].

Module Tests.

Definition dumb_def (n m : nat) := match Nat.eqb n m with true => true | false => false end.

Goal (forall n m : nat, dumb_def n m = false)-> False.
 intros. get_def dumb_def. expand_hyp dumb_def_def.
eliminate_dependent_pattern_matching H0.
get_def length. expand_hyp length_def.
eliminate_fix_hyp H0. eliminate_dependent_pattern_matching H1.
Abort.


Lemma foo x y :( if (Nat.leb x y) then 2 + 2 = 4 else 3+4 = 6) -> False.
intros. 
eliminate_dependent_pattern_matching H.
Abort.

Lemma bar: ( forall x y, if (Nat.leb x y) then 2 + 2 = 4 else 3+4 = 6) -> False.
intros. eliminate_dependent_pattern_matching H.
Abort.

Lemma toto (A : Type) (x : list A) :
match x with 
| nil => 0 = 0
| y :: ys => ys = ys
end
-> True.
Proof. intros. eliminate_dependent_pattern_matching H.
exact I. Qed.


Definition min1 (x : nat) := match x with
| 0 => 0
| S x => x
end.
Definition min1' := min1.

Definition min1'' := min1'.

Definition min1''' := min1''.


MetaCoq Quote Definition hyp_cons_reif := ((forall (A: Type) (x : A) (a : A) (l : list A), 
@hd A x (@cons A a l) = match (@cons A a l) with
| nil => x
| y :: xs => y
end)).

Definition bool_pair := (bool * bool)%type.
Inductive dep_type : Type -> Type :=
| ToBool : bool -> dep_type bool
| ToUnit : bool -> dep_type unit.

Definition dep_fun : bool -> bool_pair -> bool := fun d : bool => match d with
                      | true => fst
                      | false => snd
                      end
.

Definition dep_match : forall (ω :  bool_pair) (a : Type) (D :  dep_type a), (match D with 
| ToBool _ =>  bool 
| ToUnit _ => unit
end) -> bool :=
fun ω a D => match D with
| ToBool d => fun x => Bool.eqb (dep_fun d ω) x
| ToUnit d => fun x => true
end.


Goal True.
get_def length. expand_hyp length_def. eliminate_fix_hyp H.  
get_def Nat.add. expand_hyp add_def. eliminate_fix_hyp H1.
eliminate_dependent_pattern_matching H2.
eliminate_dependent_pattern_matching H0.
get_def dep_match. expand_hyp dep_match_def.
eliminate_fix_hyp H0.
clear - H2. eliminate_dependent_pattern_matching H2.
Abort. 

Fixpoint nth {A : Type} (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

Goal False.
get_def @nth. expand_hyp nth_def. 
eliminate_fix_hyp H.  
eliminate_dependent_pattern_matching H0.
Abort.

End Tests.
