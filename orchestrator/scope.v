From Ltac2 Require Import Ltac2.

Require Import ZArith.
Require Import PArith.BinPos.
Require Import NArith.BinNatDef.

From SMTCoq Require Import SMT_classes SMT_classes_instances BVList FArray.

From Sniper Require Import Sniper.

Require Import triggers_tactics.
Require Import triggers.
Require Import printer.
Require Import orchestrator.

Set Default Proof Mode "Classic".

From Ltac2 Require Import Printf.

Ltac2 init_triggered ():=
[("my_reflexivity", [constr:(Z.add)]);
("my_reflexivity", [constr:(Z.sub)]);
("my_reflexivity", [constr:(Z.mul)]);
("my_reflexivity", [constr:(Z.eqb)]);
("my_reflexivity", [constr:(Z.ltb)]);
("my_reflexivity", [constr:(Z.leb)]);
("my_reflexivity", [constr:(Z.geb)]);
("my_reflexivity", [constr:(Z.gtb)]);
("my_reflexivity", [constr:(Z.lt)]);
("my_reflexivity", [constr:(Z.le)]);
("my_reflexivity", [constr:(Z.ge)]);
("my_reflexivity", [constr:(Z.gt)]);
("my_reflexivity", [constr:(Pos.lt)]);
("my_reflexivity", [constr:(Pos.le)]);
("my_reflexivity", [constr:(Pos.ge)]);
("my_reflexivity", [constr:(Pos.gt)]);
("my_reflexivity", [constr:(Z.to_nat)]);
("my_reflexivity", [constr:(Pos.mul)]);
("my_reflexivity", [constr:(Pos.add)]);
("my_reflexivity", [constr:(Pos.sub)]);
("my_reflexivity", [constr:(Init.Nat.add)]);
("my_reflexivity", [constr:(Init.Nat.mul)]);
("my_reflexivity", [constr:(Nat.eqb)]);
("my_reflexivity", [constr:(Nat.leb)]);
("my_reflexivity", [constr:(Nat.ltb)]);
("my_reflexivity", [constr:(Peano.lt)]);
("my_reflexivity", [constr:(ge)]); 
("my_reflexivity", [constr:(gt)]);
("my_reflexivity", [constr:(N.add)]);
("my_reflexivity", [constr:(N.mul)]);
("my_reflexivity", [constr:(N.eqb)]);
("my_reflexivity", [constr:(N.leb)]);
("my_reflexivity", [constr:(N.ltb)]);
("my_reflexivity", [constr:(Peano.lt)]);
("my_reflexivity", [constr:(ge)]); 
("my_reflexivity", [constr:(gt)]);
("my_reflexivity", [constr:(negb)]);
("my_reflexivity", [constr:(not)]);
("my_reflexivity", [constr:(andb)]);
("my_reflexivity", [constr:(orb)]);
("my_reflexivity", [constr:(implb)]);
("my_reflexivity", [constr:(xorb)]);
("my_reflexivity", [constr:(Bool.eqb)]);
("my_reflexivity", [constr:(iff)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_eq)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_and)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_or)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_xor)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_add)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_mult)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_ult)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_slt)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_concat)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_shl)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_shr)]);
("my_reflexivity", [constr:(@FArray.select)]);
("my_reflexivity", [constr:(@FArray.diff)]);
("my_reflexivity", [constr:(is_true)]);
("my_reflexivity", [constr:(@eqb_of_compdec)]);
("my_reflexivity", [constr:(CompDec)]);
("my_reflexivity", [constr:(Nat_compdec)]);
("my_reflexivity", [constr:(list_compdec)]);
("my_reflexivity", [constr:(prod_compdec)]);
("my_reflexivity", [constr:(Z_compdec)]);
("my_algebraic_types", [constr:(Z)]);
("my_algebraic_types", [constr:(bool)]);
("my_algebraic_types", [constr:(positive)]);
("my_algebraic_types", [constr:(N)]);
("my_algebraic_types", [constr:(nat)]);
("my_algebraic_types", [constr:(EqbType)]);
("my_algebraic_types", [constr:(@CompDec)]);
("my_algebraic_types", [constr:(Comparable)]);
("my_algebraic_types", [constr:(Inhabited)]);
("my_algebraic_types", [constr:(OrderedType.Compare)]);
("my_gen_principle", [constr:(Z)]);
("my_gen_principle", [constr:(bool)]);
("my_gen_principle", [constr:(positive)]);
("my_gen_principle", [constr:(N)]);
("my_gen_principle", [constr:(nat)]);
("my_gen_principle", [constr:(EqbType)]);
("my_gen_principle", [constr:(@CompDec)]);
("my_gen_principle", [constr:(Comparable)]);
("my_gen_principle", [constr:(Inhabited)]);
("my_gen_principle", [constr:(OrderedType.Compare)]);
("my_add_compdec", [constr:(FArray.farray)]);
("my_add_compdec", [constr:(Z)]);
("my_add_compdec", [constr:(nat)]);
("my_add_compdec", [constr:(positive)]);
("my_add_compdec", [constr:(bool)])
].

Ltac my_reflexivity t := assert_refl t.

Ltac my_unfold_refl H := unfold_refl H.

(* Ltac my_trakt_bool := revert_all ; trakt bool ; intros.  *)

Ltac my_higher_order_equalities H := expand_hyp H ; clear H.

Ltac my_higher_order := prenex_higher_order_with_equations.

Ltac my_fixpoints H := eliminate_fix_hyp H.

Ltac my_pattern_matching H := try (eliminate_dependent_pattern_matching H).

Ltac my_anonymous_functions := anonymous_funs. (* TODO : wrong trigger, avoid higher order equalities (= priorities ??) *)

Ltac my_algebraic_types t := try (interp_alg_types t).

Ltac my_gen_principle t := 
 pose_gen_statement t.

Definition prod_types := (Z, bool, True, False, positive, N, and, or, nat, Init.Peano.le,
@CompDec, Comparable, EqbType, Inhabited, OrderedType.Compare).

Ltac my_gen_principle_temporary := ltac2:(get_projs_in_variables 'prod_types).

Ltac my_polymorphism_elpi := elimination_polymorphism.

Ltac my_polymorphism := inst.

Ltac my_add_compdec t := add_compdecs_terms t.

Ltac2 trigger_generation_principle := TOneTime.

Ltac2 trigger_anonymous_funs := TOneTime.


Ltac2 trigger_higher_order :=
  TOneTime.


Ltac2 scope () := orchestrator 5
{ all_tacs := 
[
("my_anonymous_functions", trigger_anonymous_funs) ;
("my_higher_order", trigger_higher_order) ; 
("my_reflexivity", trigger_reflexivity ());
("my_unfold_refl", trigger_unfold_reflexivity ()) ;
("my_higher_order_equalities", trigger_higher_order_equalities); 
("my_fixpoints", trigger_fixpoints);
("my_pattern_matching", trigger_pattern_matching);
("my_algebraic_types", trigger_algebraic_types);
("my_gen_principle_temporary", trigger_generation_principle) ;
("my_polymorphism_elpi", trigger_polymorphism ()) ;
("my_add_compdec", trigger_add_compdecs ())] }
{ triggered_tacs := (init_triggered ()) } {old_types_and_defs  := [] } Nothing.

Ltac2 scope2 () := orchestrator 5
{ all_tacs := 
[
("my_anonymous_functions", trigger_anonymous_funs) ;
("my_higher_order", trigger_higher_order) ; 
("my_reflexivity", trigger_reflexivity ());
("my_unfold_refl", trigger_unfold_reflexivity ()) ;
("my_higher_order_equalities", trigger_higher_order_equalities); 
("my_fixpoints", trigger_fixpoints);
("my_pattern_matching", trigger_pattern_matching);
("my_algebraic_types", trigger_algebraic_types);
("my_gen_principle_temporary", trigger_generation_principle) ;
("my_polymorphism", trigger_polymorphism ()) ;
("my_add_compdec", trigger_add_compdecs ())] }
{ triggered_tacs := (init_triggered ()) } {old_types_and_defs  := [] } Nothing.

Tactic Notation "scope" := ltac2:(scope ()).

Tactic Notation "scope" := ltac2:(Control.enter (fun () => scope ())).

Tactic Notation "scope2" := ltac2:(Control.enter (fun () => scope2 ())).

Local Open Scope Z_scope.

Require Import List.
Import ListNotations.


(*
Section Debug.

Variable (A : Type).
Variable (HA: CompDec A).

 Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof.
    induction x; intros ; scope.
    - verit.
    - (* TODO ??? generalize dependent app. *) generalize dependent app ; verit.
    
  Qed.

End Debug.  *)

Section higher_order.

Variable A B C: Type.
Variable HA : CompDec A.
Variable HB : CompDec B.
Variable HC : CompDec C.

Fixpoint zip {A B : Type} (l : list A) (l' : list B) :=
  match l, l' with
  | [], _ => []
  | x :: xs, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys 
  end.
(* 
Lemma zip_map : forall (f : A -> B) (g : A -> C) (l : list A),
map (fun (x : A) => (f x, g x)) l = zip (map f l) (map g l).
Proof.
intros f g l ; induction l; time (scope; verit).
(* Tactic call ran for 94.262 secs (93.569u,0.299s) (success) *) Abort. *)

Lemma map_compound : forall (f : A -> B) (g : B -> C) (l : list A), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
induction l; time scope. verit_no_check. verit.
Qed.


End higher_order.

(** Examples on lists *)

(* A simple example *)
Goal forall (l : list Z) (x : Z), hd_error l = Some x -> (l <> nil).
(* Proof.
(* Time snipe. (* Finished transaction in 2.783 secs (2.428u,0.007s) (successful) *) *)
Undo. *)
Time scope; verit_no_check. 
Qed.

Section Generic.

  Variable (A : Type).
  Hypothesis HA : CompDec A.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof.
  Time scope; verit_no_check. (* Finished transaction in 0.549 secs (0.516u,0.s) (successful) *)
(* Undo.
  Time snipe. (* Finished transaction in 3.028 secs (2.64u,0.015s) (successful) *) *)
  Qed.

End Generic.

Require Import List.
Import ListNotations.

Section destruct_auto.

  Variable A : Type.
  Variable HA : CompDec A.

Theorem app_eq_unit_auto :
    forall (x y: list A) (a:A),
      x ++ y = a :: nil -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof. 
intros ; scope; verit_no_check.
Qed.


End destruct_auto.

Require Import Bool.


(* Example of searching an element in a list *)
Fixpoint search {A : Type} {H: CompDec A} (x : A) l :=
  match l with
  | [] => false
  | x0 :: l0 => eqb_of_compdec H x x0 || search x l0
  end.

(* Lemma search_app_snipe : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof. intros A H x l1 l2.
Time induction l1 as [ | x0 l0 IH]; ltac2:(Control.enter (fun () => scope ())). 
- generalize  dependent search. verit.
(* Finished transaction in 1.518 secs (1.456u,0.019s) (successful) *)
(* Time induction l1 as [ | x0 l0 IH]; simpl; snipe Finished transaction in 9.089 secs (7.921u,0.005s) (successful). *)

Qed. *)

Lemma search_app : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
  intros A H x l1 l2. induction l1 as [ | x0 l0 IH].
  - reflexivity.
  - simpl. destruct (eqb_of_compdec H x x0).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* It can be fully automatized *)
Lemma snipe_search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A),
search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof. intros A H. 

(* Time snipe @search_app. Finished transaction in 5.777 secs (5.007u,0.s) (successful) *)
(* Undo. *)
pose proof search_app.
Time scope; verit_no_check. (* Finished transaction in 0.842 secs (0.76u,0.007s) (successful) *)


Qed.


(* Another example with search *)
Lemma in_inv : forall (A: Type) (HA : CompDec A) (a b:A) (l:list A),
    search b (a :: l) -> eqb_of_compdec HA a b \/ search b l.
Proof. intros A HA.  
(* Time snipe. *) (* Finished transaction in 2.652 secs (2.239u,0.s) (successful) *)
(* Undo. *)
Time scope; verit_no_check. (* Finished transaction in 0.434 secs (0.405u,0.s) (successful) *)

Qed.


(* Another example with an induction *)
Lemma app_nil_r : forall (A: Type) (H: CompDec A) (l:list A), (l ++ [])%list = l.
Proof. 
(*  intros A H. Time induction l; snipe. *) (* Finished transaction in 4.195 secs (3.601u,0.s) (successful) *)
(* Undo. *)
Time induction l ; ltac2:(Control.enter (fun () => scope ())) ; verit_no_check. 
(* Finished transaction in 0.952 secs (0.902u,0.s) (successful) *)

Qed.

From Sniper Require Import tree.

(** Examples on trees *)

Lemma empty_tree_Z2 : forall (t : @tree Z) a t' b,
is_empty t = true -> t <> Node a t' b.
Proof. (* Time intros t a t' b; snipe. (* 2.752 s *)
Undo. *)
Time intros t a t' b ; ltac2:(Control.enter (fun () => scope ())) ; verit_no_check.
(* Finished transaction in 0.785 secs (0.754u,0.s) (successful) *)
Qed.

(* TODO try with the other elim poly strat Lemma rev_elements_app :
 forall A (H:CompDec A) s acc, tree.rev_elements_aux A acc s = ((tree.rev_elements A s) ++ acc)%list.
Proof. intros A H s ; induction s.
- Time snipe app_nil_r. (* Finished transaction in 8.973 secs (7.871u,0.007s) (successful) *)
Undo. pose proof List.app_nil_r. Time scope; verit.
- snipe (app_ass, app_nil_r).
Qed.
 *)

Lemma rev_elements_app :
 forall A (H:CompDec A) s acc, tree.rev_elements_aux A acc s = ((tree.rev_elements A s) ++ acc)%list.
Proof. intros A H s ; induction s.
- (* snipe app_nil_r. Undo.  *)pose proof List.app_nil_r. scope; verit_no_check.
- pose proof List.app_ass. pose proof List.app_nil_r. scope. verit_no_check.
Qed.


Lemma rev_elements_node c (H: CompDec c) l x r :
 rev_elements c (Node l x r) = (rev_elements c r ++ x :: rev_elements c l)%list.
Proof. (* Time snipe (rev_elements_app, app_nil_r).  *)
(* Finished transaction in 11.955 secs (10.477u,0.007s) (successful) *)
(* Undo. *)
pose proof rev_elements_app.
pose proof List.app_nil_r.
scope; verit_no_check. Qed.










   