From Sniper Require Import Sniper.
Require Import List Bool.
Require Import PeanoNat.

Set Implicit Arguments.

#[local] Open Scope bool_scope.
Open Scope list_scope.

Import ListNotations.

Section Lists.

  Variable A : Type.

  (** Head and tail *)

  Definition hd (default:A) (l:list A) :=
    match l with
      | [] => default
      | x :: _ => x
    end.

  Definition hd_error (l:list A) :=
    match l with
      | [] => None
      | x :: _ => Some x
    end.

  Definition tl (l:list A) :=
    match l with
      | [] => nil
      | a :: m => m
    end.

  (** The [In] predicate *)
  Fixpoint In (a:A) (l:list A) : Prop :=
    match l with
      | [] => False
      | b :: m => b = a \/ In a m
    end.

End Lists.

Section Facts.

  Variable A : Type.
  Variable HA : CompDec A. 

  (** *** Generic facts *)

  (** Discrimination *)
  Theorem nil_cons (x:A) (l:list A) : [] <> x :: l.
  Proof. idtac "nil_cons".
   Time snipe.
  Qed.


  (** Destruction *)

  Theorem destruct_list (l : list A) : {x:A & {tl:list A | l = x::tl}}+{l = []}.
  Proof. idtac "destruct_list".
    induction l as [|a tail].
    right; reflexivity.
    left; exists a, tail; reflexivity.
  Qed. 

  Lemma hd_error_tl_repr l (a:A) r :
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. idtac "hd_error_tl_repr".
    Time snipe.
  Qed.

  Lemma hd_error_some_nil l (a:A) : hd_error l = Some a -> l <> nil.
  Proof. idtac "hd_error_some_nil". Time snipe.  Qed.

  Theorem length_zero_iff_nil (l : list A):
    length l = 0 <-> l = [].
  Proof. idtac "length_zero_iff_nil".
  split; [now destruct l | now intros ->].
  Qed.

  (** *** Head and tail *)

  Theorem hd_error_nil : hd_error (@nil A) = None.
  Proof. idtac "hd_error_nil".
    Time snipe.
  Qed.

  Theorem hd_error_cons (l : list A) (x : A) : hd_error (x::l) = Some x.
  Proof. idtac "hd_error_cons".
   Time snipe.
  Qed.


  (**************************)
  (** *** Facts about [app] *)
  (**************************)

  (** Discrimination *)
  Theorem app_cons_not_nil (x y:list A) (a:A) : [] <> x ++ a :: y.
  Proof. idtac "app_cons_not_nil".
    Time snipe.
  Qed.


  (** Concat with [nil] *)
  Theorem app_nil_l (l:list A) : [] ++ l = l.
  Proof. idtac "app_nil_l".
   Time snipe.
  Qed.

  Theorem app_nil_r (l:list A) : l ++ [] = l.
  Proof. idtac "app_nil_r".
    Time induction l; snipe.
  Qed.

  Theorem app_nil_end (l:list A) : l = l ++ [].
  Proof. idtac "app_nil_end". Time induction l; snipe. Qed.

  (** [app] is associative *)
  Theorem app_assoc (l m n:list A) : l ++ m ++ n = (l ++ m) ++ n.
  Proof. idtac "app_assoc".
   Time induction l; snipe.
  Qed.

  Theorem app_assoc_reverse (l m n:list A) : (l ++ m) ++ n = l ++ m ++ n.
  Proof. idtac "app_assoc_reverse". Time snipe @app_assoc. Qed.
  (* end hide *)

  (** [app] commutes with [cons] *)
  Theorem app_comm_cons (x y:list A) (a:A) : a :: (x ++ y) = (a :: x) ++ y.
  Proof. idtac "app_comm_cons".
   Time snipe.
  Qed.

  (** Facts deduced from the result of a concatenation *)

  Theorem app_eq_nil (l l':list A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof. idtac "app_eq_nil".
   Time snipe.
  Qed.

  Theorem app_eq_unit (x y:list A) (a:A) :
      x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof. idtac "app_eq_unit".
    Time snipe.
  Qed.

  Lemma elt_eq_unit l1 l2 (a b : A) :
    l1 ++ a :: l2 = [b] -> a = b /\ l1 = [] /\ l2 = [].
  Proof. idtac "elt_eq_unit".
   Time snipe @app_eq_unit. 
  Qed.

  Theorem app_eq_app X (x1 x2 y1 y2: list X) : x1++x2 = y1++y2 ->
    exists l, (x1 = y1++l /\ y2 = l++x2) \/ (y1 = x1++l /\ x2 = l++y2).
  Proof. idtac "app_eq_app".
   revert y1. induction x1 as [|a x1 IH].
    - cbn. intros y1 ->. exists y1. now right.
    - intros [|b y1]; cbn.
      + intros <-. exists (a :: x1). now left.
      + intros [=-> [l Hl] %IH]. exists l.
        now destruct Hl as [[-> ->]|[-> ->]]; [left|right].
  Qed.

  Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof. idtac "app_inj_tail".
    Time induction x; snipe.
  Qed.

  Lemma app_inj_tail_iff :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] <-> x = y /\ a = b.
  Proof. idtac "app_inj_tail_iff".
   Time snipe @app_inj_tail.
  Qed.

  (** Compatibility with other operations *)

  Lemma app_length : forall l l' : list A, length (l++l') = length l + length l'.
  Proof. idtac "app_length".
   Time intro l; induction l; snipe.
  Qed.

  Lemma last_length : forall (l : list A) a, length (l ++ a :: nil) = S (length l).
  Proof. idtac "last_length".
   Time snipe @app_length.
  Qed.

  Lemma app_inv_head_iff:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 <-> l1 = l2.
  Proof. idtac "app_inv_head_iff".
    intro l; induction l as [|? l IHl]; split; intros H; simpl; auto.
    - apply IHl. inversion H. auto.
    - subst. auto.
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof. idtac "app_inv_head:
  ".
    Time intro l ; induction l ; snipe.
  Qed.

  Lemma app_inv_tail:
    forall l l1 l2 : list A, l1 ++ l = l2 ++ l -> l1 = l2.
  Proof. idtac "app_inv_tail:
   ".
    intros l. induction l as [|a l IHl].
    - intros ? ?. now rewrite !app_nil_r.
    - intros ? ?. change (a :: l) with ([a] ++ l).
      rewrite !app_assoc. now intros [? ?] %IHl %app_inj_tail_iff.
  Qed.

  Lemma app_inv_tail_iff:
    forall l l1 l2 : list A, l1 ++ l = l2 ++ l <-> l1 = l2.
  Proof. idtac "app_inv_tail_iff:
   ".
   Time snipe @app_inv_tail.
  Qed.

  (************************)
  (** *** Facts about [In] *)
  (************************)


  (** Characterization of [In] *)

  (** These lemmas can be automatized for a boolean version of In **)

 Definition  Inb := 
  fun (A : Type) {HA : CompDec A} =>
  fix Inb (a : A) (l : list A) {struct l} : bool :=
    match l with
    | [] => false
    | b :: m => orb (eqb_of_compdec HA a b) (Inb a m)
    end.

  Theorem inb_eq : forall (a:A) (l:list A), Inb a (a :: l).
  Proof. idtac "inb_eq".
   Time snipe.
  Qed.

  Theorem inb_cons : forall (a b:A) (l:list A), Inb b l -> Inb b (a :: l).
  Proof. idtac "inb_cons".
   Time snipe.
  Qed.

  Theorem not_inb_cons (x a : A) (l : list A):
    negb (Inb x (a::l)) <-> x<>a /\ negb (Inb x l).
  Proof. idtac "not_inb_cons".
   Time snipe.
  Qed.

  Theorem inb_nil : forall a:A, negb (Inb a []).
  Proof. idtac "inb_nil".
    Time snipe.
  Qed.

  Lemma inb_app_or : forall (l m:list A) (a:A), Inb a (l ++ m) -> Inb a l \/ Inb a m.
  Proof. idtac "inb_app_or".
   Time intros l ; induction l; snipe. Qed.

  Lemma inb_or_app : forall (l m:list A) (a:A), orb (Inb a l) (Inb a m) -> Inb a (l ++ m).
  Proof. idtac "inb_or_app".
   Time intros l ; induction l ; snipe.
  Qed.

  Lemma inb_app_iff : forall l l' (a:A), Inb a (l++l') <-> Inb a l \/ Inb a l'.
  Proof. idtac "inb_app_iff".
   Time snipe (@inb_app_or, @inb_or_app). 
  Qed.

  Theorem inb_split : forall x (l:list A), In x l -> exists l1 l2, l = l1++x::l2.
  Proof. idtac "inb_split".
  intros x l; induction l as [|a l IHl]; simpl; [destruct 1|destruct 1 as [?|H]].
  subst a; auto.
  exists [], l; auto.
  destruct (IHl H) as (l1,(l2,H0)).
  exists (a::l1), l2; simpl. apply f_equal. auto.
  Qed.

  Lemma inb_elt : forall (x:A) l1 l2, Inb x (l1 ++ x :: l2).
  Proof. idtac "inb_elt".
  Time snipe @inb_or_app.
  Qed.

  Lemma in_elt_inv : forall (x y : A) l1 l2,
    Inb x (l1 ++ y :: l2) -> x = y \/ Inb x (l1 ++ l2).
  Proof. idtac "in_elt_inv". 
  Time snipe (inb_or_app, inb_app_or).
  Qed.

  (** Inversion *)
  Lemma in_inv : forall (a b:A) (l:list A), Inb b (a :: l) -> a = b \/ Inb b l.
  Proof. idtac "in_inv". Time snipe. Qed.

  (** Decidability of [In] *)
  Theorem in_dec :
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (a:A) (l:list A), {In a l} + {~ In a l}.
  Proof. idtac "in_dec".
    intros H a l; induction l as [| a0 l IHl].
    right; apply in_nil.
    destruct (H a0 a); simpl; auto.
    destruct IHl; simpl; auto.
    right; unfold not; intros [Hc1| Hc2]; auto.
  Defined.

End Facts.

(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.
  Variable HA : CompDec A.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

  Fixpoint nth_ok (n:nat) (l:list A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, other => false
      | S m, [] => false
      | S m, x :: t => nth_ok m t default
    end.

  Lemma nth_in_or_default :
    forall (n:nat) (l:list A) (d:A), {In (nth n l d) l} + {nth n l d = d}.
  Proof. idtac "nth_in_or_default".
      intros n l d; revert n; induction l as [|? ? IHl].
    - intro n; right; destruct n; trivial.
    - intros [|n]; simpl.
      * left; auto.
      * destruct (IHl n); auto.
  Qed.

  Lemma nth_S_cons :
    forall (n:nat) (l:list A) (d a:A),
      Inb (nth n l d) l -> Inb (nth (S n) (a :: l) d) (a :: l).
  Proof. idtac "nth_S_cons".
   Time snipe.
  Qed.

  Fixpoint nth_error (l:list A) (n:nat) {struct n} : option A :=
    match n, l with
      | O, x :: _ => Some x
      | S n, _ :: l => nth_error l n
      | _, _ => None
    end.

  Definition nth_default (default:A) (l:list A) (n:nat) : A :=
    match nth_error l n with
      | Some x => x
      | None => default
    end.

(** Pattern matching not on a variable **)

  Lemma nth_default_eq :
    forall n l (d:A), nth_default d l n = nth n l d.
  Proof. idtac "nth_default_eq".
    unfold nth_default; intro n; induction n; intros [ | ] ?; simpl; auto.
  Qed.

  (** Results about [nth] *)

  Lemma nth_In :
    forall (n:nat) (l:list A) (d:A), n < length l -> Inb (nth n l d) l.
  Proof. idtac "nth_In".
   Time intro n ; induction n ; snipe.
  Qed.

  Lemma Inb_nth l x d : Inb x l ->
    exists n, n < length l /\ nth n l d = x.
  Proof. idtac "Inb_nth".
     induction l as [|a l IH].
    - easy.
    - intros H. simpl in H. unfold orb in H.
    destruct (eqb_of_compdec HA x a) eqn : E.
      * exists 0. simpl. split. auto using Nat.lt_0_succ. 
rewrite <- compdec_eq_eqb in E. symmetry. assumption. 
      * destruct (IH H) as (n & Hn & Hn').
        apply Nat.succ_lt_mono in Hn. now exists (S n).
  Qed.

  Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
  Proof. idtac "nth_overflow".
      intro l; induction l as [|? ? IHl]; intro n; destruct n;
     simpl; intros d H; auto.
    - inversion H.
    - apply IHl. now apply Nat.succ_le_mono.
  Qed.

  Lemma nth_indep :
    forall l n d d', n < length l -> nth n l d = nth n l d'.
  Proof. idtac "nth_indep".
    intro l; induction l as [|? ? IHl].
    - inversion 1.
    - intros [|n] d d'; [intros; reflexivity|].
      intros H. apply IHl. now apply Nat.succ_lt_mono.
  Qed.

  Lemma app_nth1 :
    forall l l' d n, n < length l -> nth n (l++l') d = nth n l d.
  Proof. idtac "app_nth1".
      intro l; induction l as [|? ? IHl].
    - inversion 1.
    - intros l' d [|n]; simpl; [intros; reflexivity|].
      intros H. apply IHl. now apply Nat.succ_lt_mono.
    Qed.

  Lemma app_nth2 :
    forall l l' d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
  Proof. idtac "app_nth2".
      intro l; induction l as [|? ? IHl]; intros l' d [|n]; auto.
    - inversion 1.
    - intros; simpl; rewrite IHl; [reflexivity|now apply Nat.succ_le_mono].
  Qed.

  Lemma app_nth2_plus : forall l l' d n,
    nth (length l + n) (l ++ l') d = nth n l' d.
  Proof. idtac "app_nth2_plus".
    intros.
    now rewrite app_nth2, Nat.add_comm, Nat.add_sub; [|apply Nat.le_add_r].
  Qed.

  Lemma nth_middle : forall l l' a d,
    nth (length l) (l ++ a :: l') d = a.
  Proof. idtac "nth_middle".
   Time snipe @app_nth2_plus.
  Qed.

  Lemma nth_split n l d : n < length l ->
    exists l1, exists l2, l = l1 ++ nth n l d :: l2 /\ length l1 = n.
  Proof. idtac "nth_split".
    revert l.
    induction n as [|n IH]; intros [|a l] H; try easy.
    - exists nil; exists l; now simpl.
    - destruct (IH l) as (l1 & l2 & Hl & Hl1); [now apply Nat.succ_lt_mono|].
      exists (a::l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma nth_ext : forall l l' d d', length l = length l' ->
    (forall n, n < length l -> nth n l d = nth n l' d') -> l = l'.
  Proof. idtac "nth_ext".
    intro l; induction l as [|a l IHl];
     intros l' d d' Hlen Hnth; destruct l' as [| b l'].
    - reflexivity.
    - inversion Hlen.
    - inversion Hlen.
    - change a with (nth 0 (a :: l) d).
      change b with (nth 0 (b :: l') d').
      rewrite Hnth; f_equal.
      + apply IHl with d d'; [ now inversion Hlen | ].
        intros n Hlen'; apply (Hnth (S n)).
        now apply (Nat.succ_lt_mono n (length l)).
      + simpl; apply Nat.lt_0_succ.
  Qed.

  (** Results about [nth_error] *)


  Lemma nth_error_Inb l n x : nth_error l n = Some x -> Inb x l.
  Proof. idtac "nth_error_Inb".
    revert n. induction l as [|a l IH].
    - intros n. simpl. intros H. destruct n; simpl in H; inversion H.
    - intros n. intros H. destruct n. simpl in H. inversion H. 
    unfold Inb. unfold orb. destruct (eqb_of_compdec HA x x) eqn : E. 
  constructor. rewrite Typ.eqb_compdec_spec_false in E.
  elim E. reflexivity. 
  simpl in H. apply IH in H. simpl. unfold orb. destruct (eqb_of_compdec HA x a); 
  [constructor | assumption].
  Qed.

  Lemma Inb_nth_error l x : Inb x l -> exists n, nth_error l n = Some x.
  Proof. idtac "Inb_nth_error".
     induction l as [|a l IH].
    - easy.
    - simpl. unfold orb. destruct (eqb_of_compdec HA x a) eqn: E.
      + exists 0. rewrite Typ.eqb_compdec_spec in E. simpl. apply f_equal.
      symmetry; assumption.
      + intros H. apply IH in H. destruct H as [x0 H]. exists (S x0). simpl.
  assumption. Qed.

  Lemma nth_error_None l n : nth_error l n = None <-> length l <= n.
  Proof. idtac "nth_error_None".
      revert n. induction l as [|? ? IHl]; intro n; destruct n; simpl.
    - split; auto.
    - now split; intros; [apply Nat.le_0_l|].
    - now split; [|intros ? %Nat.nle_succ_0].
    - now rewrite IHl, Nat.succ_le_mono.
  Qed. 


  Lemma nth_error_Some l n : nth_error l n <> None <-> n < length l.
  Proof. idtac "nth_error_Some".
     revert n. induction l as [|? ? IHl]; intro n; destruct n; simpl.
    - split; [now destruct 1 | inversion 1].
    - split; [now destruct 1 | inversion 1].
    - now split; intros; [apply Nat.lt_0_succ|].
    - now rewrite IHl, Nat.succ_lt_mono.
  Qed.

  Lemma nth_error_split l n a : nth_error l n = Some a ->
    exists l1, exists l2, l = l1 ++ a :: l2 /\ length l1 = n.
  Proof. idtac "nth_error_split".
    revert l.
    induction n as [|n IH]; intros [|x l] H; [easy| |easy|].
    - exists nil; exists l. now injection H as [= ->].
    - destruct (IH _ H) as (l1 & l2 & H1 & H2).
      exists (x::l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma nth_error_app1 l l' n : n < length l ->
    nth_error (l++l') n = nth_error l n.
  Proof. idtac "nth_error_app1".
    revert l.
    induction n as [|n IHn]; intros [|a l] H; [easy ..|].
    cbn. now apply IHn, Nat.succ_le_mono.
  Qed.

  (** Minus not handled **)
  Lemma nth_error_app2 l l' n : length l <= n ->
    nth_error (l++l') n = nth_error l' (n-length l).
  Proof. idtac "nth_error_app2".
    revert l.
    induction n as [|n IHn]; intros [|a l] H; [easy ..|].
    cbn. now apply IHn, Nat.succ_le_mono.
  Qed.

  (** Results directly relating [nth] and [nth_error] *)

  Lemma nth_error_nth : forall (l : list A) (n : nat) (x d : A),
    nth_error l n = Some x -> nth n l d = x.
  Proof. idtac "nth_error_nth".
    intros l n x d H.
    apply nth_error_split in H. destruct H as [l1 [l2 [H H']]].
    subst. rewrite app_nth2; [|auto].
    rewrite Nat.sub_diag. reflexivity.
  Qed.

  Lemma nth_error_nth' : forall (l : list A) (n : nat) (d : A),
    n < length l -> nth_error l n = Some (nth n l d).
  Proof. idtac "nth_error_nth'".
    intros l n d H.
    apply (nth_split _ d) in H. destruct H as [l1 [l2 [H H']]].
    subst. rewrite H. rewrite nth_error_app2; [|auto].
    rewrite app_nth2; [| auto]. repeat (rewrite Nat.sub_diag). reflexivity.
  Qed.

  (******************************)
  (** ** Last element of a list *)
  (******************************)

  (** [last l d] returns the last element of the list [l],
    or the default value [d] if [l] is empty. *)

  Fixpoint last (l:list A) (d:A) : A :=
  match l with
    | [] => d
    | [a] => a
    | a :: l => last l d
  end.

  Lemma last_last : forall l a d, last (l ++ [a]) d = a.
  Proof. idtac "last_last".
   Time intro l ; induction l ; snipe.
  Qed.

  (** [removelast l] remove the last element of [l] *)

  Fixpoint removelast (l:list A) : list A :=
    match l with
      | [] =>  []
      | [a] => []
      | a :: l => a :: removelast l
    end.

  Lemma app_removelast_last :
    forall l d, l <> [] -> l = removelast l ++ [last l d].
  Proof. idtac "app_removelast_last".
    intro l; induction l as [|? l IHl].
    destruct 1; auto.
    intros d _.
    destruct l as [|a0 l]; auto.
    pattern (a0::l) at 1; rewrite IHl with d; auto; discriminate.
  Qed.

  Lemma exists_last :
    forall l, l <> [] -> { l' : (list A) & { a : A | l = l' ++ [a]}}.
  Proof. idtac "exists_last".
    intro l; induction l as [|a l IHl].
    destruct 1; auto.
    intros _.
    destruct l.
    exists [], a; auto.
    destruct IHl as [l' (a',H)]; try discriminate.
    rewrite H.
    exists (a::l'), a'; auto.
  Qed.

  Lemma removelast_app :
    forall l l', l' <> [] -> removelast (l++l') = l ++ removelast l'.
  Proof. idtac "removelast_app".
    intro l; induction l as [|? l IHl]; [easy|].
    intros l' H. cbn. rewrite <- IHl by assumption.
    now destruct l, l'.
  Qed.

  Lemma removelast_last : forall l a, removelast (l ++ [a]) = l.
  Proof. idtac "removelast_last".
    intros. rewrite removelast_app.
    - apply app_nil_r.
    apply HA ; intros Heq; inversion Heq. 
  - unfold "<>". intros.
  inversion H.
  Qed.


  (*****************)
  (** ** Remove : CompDec Version  *)
  (*****************)

  Fixpoint removeCd (x : A) (l : list A) : list A :=
    match l with
      | [] => []
      | y::tl => match eqb_of_compdec HA x y with 
                  | true => removeCd x tl
                  | false => y::(removeCd x tl)
                  end
    end.

  Lemma remove_cons_cd : forall x l, removeCd x (x :: l) = removeCd x l.
  Proof. idtac "remove_cons_cd".
   intros x l; simpl; destruct (eqb_of_compdec HA x x) eqn : E.
   - reflexivity.
   - apply Typ.eqb_compdec_spec_false in E. elim E; reflexivity. Qed. 

  Lemma remove_app : forall x l1 l2,
    removeCd x (l1 ++ l2) = removeCd x l1 ++ removeCd x l2.
  Proof. idtac "remove_app".
      intros x l1; induction l1 as [|a l1 IHl1]; intros l2; simpl.
    - reflexivity.
    - destruct (eqb_of_compdec HA x a).
      + apply IHl1.
      + rewrite <- app_comm_cons; f_equal.
        apply IHl1. assumption.
  Qed.

  Theorem remove_In : forall (l : list A) (x : A), negb (Inb x (removeCd x l)).
  Proof. idtac "remove_In".
    intro l; induction l as [|x l IHl]; auto.
    intro y; simpl; destruct (eqb_of_compdec HA y x) eqn: B.
    apply IHl.
    unfold negb. destruct (Inb y (x :: removeCd y l)) eqn : E.
simpl in E. unfold orb in E. rewrite B in E. specialize (IHl y).
unfold negb in IHl. rewrite E in IHl. inversion IHl. 
constructor.
  Qed.

  Lemma notin_remove: forall l x, negb (Inb x l) -> removeCd x l = l.
    Proof. idtac "notin_remove:".
      intros l x; induction l as [|y l IHl]; simpl; intros Hnin.
    - reflexivity.
    - destruct (eqb_of_compdec HA x y) eqn: E.
      * simpl in Hnin. discriminate Hnin.
      * simpl in Hnin. apply IHl in Hnin. rewrite Hnin. reflexivity. 
  Qed.

  Lemma in_remove: forall l x y, Inb x (removeCd y l) -> Inb x l /\ x <> y.
  Proof. idtac "in_remove:".
   intro l; induction l as [|z l IHl]; intros x y Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct (eqb_of_compdec HA y z) eqn:E.
      + rewrite Typ.eqb_compdec_spec in E. subst. apply IHl in Hin.
  simpl. destruct (eqb_of_compdec HA x z). simpl. destruct Hin. auto.
  simpl. assumption.
      + simpl in Hin. destruct (eqb_of_compdec HA x z) eqn : B.
 simpl in Hin.   
      simpl. rewrite B. simpl. rewrite Typ.eqb_compdec_spec_false in E. rewrite 
Typ.eqb_compdec_spec in B. rewrite <- B in E. auto.
      simpl in Hin. destruct orb. exact false. exact false.
        * apply IHl in Hin. simpl. rewrite B. simpl. auto.
        * 
apply IHl in Hin. split. simpl. rewrite B. destruct Hin. simpl. assumption.
destruct Hin. assumption.
  Qed.

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Lemma in_in_remove : forall (l : list A) x y, x <> y -> In x l -> In x (remove eq_dec y l).
  Proof. idtac "in_in_remove".
   intro l; induction l as [|z l IHl]; simpl; intros x y Hneq Hin.
    - apply Hin.
    - destruct (eq_dec y z); subst.
      + destruct Hin.
        * exfalso; now apply Hneq.
        * now apply IHl.
      + simpl; destruct Hin; [now left|right].
        now apply IHl.
  Qed. 

  Lemma remove_remove_comm : forall (l : list A) x y,
    remove eq_dec x (remove eq_dec y l) = remove eq_dec y (remove eq_dec x l).
  Proof. idtac "remove_remove_comm".
   intro l; induction l as [| z l IHl]; simpl; intros x y.
    - reflexivity.
    - destruct (eq_dec y z); simpl; destruct (eq_dec x z); try rewrite IHl; auto.
      + subst; symmetry; apply remove_cons.
      + simpl; destruct (eq_dec y z); tauto.
  Qed.

  Lemma remove_remove_eq : forall l x, removeCd x (removeCd x l) = removeCd x l.
  Proof. idtac "remove_remove_eq". intros l x; now rewrite (notin_remove _ _ (remove_In l x)). Qed.

  Lemma remove_length_le : forall l x, length (remove eq_dec x l) <= length l.
  Proof. idtac "remove_length_le".
    intro l; induction l as [|y l IHl]; simpl; intros x; trivial.
    destruct (eq_dec x y); simpl.
    - rewrite IHl; constructor; reflexivity.
    - apply (proj1 (Nat.succ_le_mono _ _) (IHl x)).
  Qed.

  Lemma remove_length_lt : forall l x, In x l -> length (remove eq_dec x l) < length l.
  Proof. idtac "remove_length_lt".
   intro l; induction l as [|y l IHl]; simpl; intros x Hin.
    - contradiction Hin.
    - destruct Hin as [-> | Hin].
      + destruct (eq_dec x x); [|easy].
        apply Nat.lt_succ_r, remove_length_le.
      + specialize (IHl _ Hin); destruct (eq_dec x y); simpl; auto.
        now apply Nat.succ_lt_mono in IHl.
 Qed. 


 (******************************************)
  (** ** Counting occurrences of an element *)
  (******************************************)

  Fixpoint count_occ (l : list A) (x : A) : nat :=
    match l with
      | [] => 0
      | y :: tl =>
        let n := count_occ tl x in
        if eq_dec y x then S n else n
    end.

  (** Compatibility of count_occ with operations on list *)
  Theorem count_occ_In l x : In x l <-> count_occ l x > 0.
  Proof. idtac "count_occ_In".
    induction l as [|y l IHl]; simpl.
    - split; [destruct 1 | apply Nat.nlt_0_r].
    - destruct eq_dec as [->|Hneq]; rewrite IHl; intuition (apply Nat.lt_0_succ).
  Qed.

  Theorem count_occ_not_In l x : ~ In x l <-> count_occ l x = 0.
  Proof. idtac "count_occ_not_In".
    rewrite count_occ_In. unfold gt. now rewrite Nat.nlt_ge, Nat.le_0_r.
  Qed.

  Lemma count_occ_nil x : count_occ [] x = 0.
  Proof. idtac "count_occ_nil".
    reflexivity.
  Qed.

  Theorem count_occ_inv_nil l :
    (forall x:A, count_occ l x = 0) <-> l = [].
  Proof. idtac "count_occ_inv_nil".
    split.
    - induction l as [|x l]; trivial.
      intros H. specialize (H x). simpl in H.
      destruct eq_dec as [_|NEQ]; [discriminate|now elim NEQ].
    - now intros ->.
  Qed.

  Lemma count_occ_cons_eq l x y :
    x = y -> count_occ (x::l) y = S (count_occ l y).
  Proof. idtac "count_occ_cons_eq".
    intros H. simpl. now destruct (eq_dec x y).
  Qed.

  Lemma count_occ_cons_neq l x y :
    x <> y -> count_occ (x::l) y = count_occ l y.
  Proof. idtac "count_occ_cons_neq".
    intros H. simpl. now destruct (eq_dec x y).
  Qed.

  Lemma count_occ_app l1 l2 x :
    count_occ (l1 ++ l2) x = count_occ l1 x + count_occ l2 x.
  Proof. idtac "count_occ_app".
    induction l1 as [ | h l1 IHl1]; cbn; trivial.
    now destruct (eq_dec h x); [ rewrite IHl1 | ].
  Qed.

  Lemma count_occ_elt_eq l1 l2 x y : x = y ->
    count_occ (l1 ++ x :: l2) y = S (count_occ (l1 ++ l2) y).
  Proof. idtac "count_occ_elt_eq".
    intros ->.
    rewrite ? count_occ_app; cbn.
    destruct (eq_dec y y) as [Heq | Hneq];
      [ apply Nat.add_succ_r | now contradiction Hneq ].
  Qed.

  Lemma count_occ_elt_neq l1 l2 x y : x <> y ->
    count_occ (l1 ++ x :: l2) y = count_occ (l1 ++ l2) y.
  Proof. idtac "count_occ_elt_neq".
    intros Hxy.
    rewrite ? count_occ_app; cbn.
    now destruct (eq_dec x y) as [Heq | Hneq]; [ contradiction Hxy | ].
  Qed.

  Lemma count_occ_bound x l : count_occ l x <= length l.
  Proof. idtac "count_occ_bound".
    induction l as [|h l]; cbn; auto.
    destruct (eq_dec h x); [ apply (proj1 (Nat.succ_le_mono _ _)) | ]; intuition.
  Qed.


End Elts.

(*******************************)
(** * Manipulating whole lists *)
(*******************************)

Section ListOps.

  Variable A : Type.
  Variable HA : CompDec A.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Fixpoint rev (l:list A) : list A :=
    match l with
      | [] => []
      | x :: l' => rev l' ++ [x]
    end.

  Lemma rev_app_distr : forall x y:list A, rev (x ++ y) = rev y ++ rev x.
  Proof. idtac "rev_app_distr".
   Time intros x ; induction x ; snipe (@app_nil_r, @app_assoc).
  Qed.

  Remark rev_unit : forall (l:list A) (a:A), rev (l ++ [a]) = a :: rev l.
  Proof. idtac "rev_unit".
   Time snipe rev_app_distr.
  Qed.

  Lemma rev_involutive : forall l:list A, rev (rev l) = l.
  Proof. idtac "rev_involutive".
  Time intro l ; induction l ; snipe @rev_unit.
  Qed.

  Lemma rev_eq_app : forall l l1 l2, rev l = l1 ++ l2 -> l = rev l2 ++ rev l1.
  Proof. idtac "rev_eq_app".
  Time  snipe (@rev_involutive, @rev_app_distr).
  Qed.

  (*********************************************)
  (** Reverse Induction Principle on Lists     *)
  (*********************************************)

  Lemma rev_list_ind : forall P:list A-> Prop,
    P [] ->
    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list A, P (rev l).
  Proof. idtac "rev_list_ind".
     intros P ? ? l; induction l; auto.
   Qed.

  Theorem rev_ind : forall P:list A -> Prop,
    P [] ->
    (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
  Proof. idtac "rev_ind".
  intros P ? ? l. rewrite <- (rev_involutive l).
  apply (rev_list_ind P); cbn; auto.
  Qed.
  

  (** Compatibility with other operations *)

  Lemma in_rev : forall l x, In x l <-> In x (rev l).
  Proof. idtac "in_rev".
    intro l; induction l as [|? ? IHl]; [easy|].
    intros. cbn. rewrite in_app_iff, IHl. cbn. tauto.
  Qed.

  Lemma rev_length : forall l, length (rev l) = length l.
  Proof. idtac "rev_length".
    Time intro l ; induction l ; snipe app_length.
  Qed.

  Lemma rev_nth : forall l d n, n < length l ->
    nth n (rev l) d = nth (length l - S n) l d.
  Proof. idtac "rev_nth".
    intros l d; induction l as [|a l IHl] using rev_ind; [easy|].
    rewrite rev_app_distr, app_length, Nat.add_comm. cbn. intros [|n].
    - now rewrite Nat.sub_0_r, nth_middle.
    - intros Hn %Nat.succ_lt_mono.
      rewrite (IHl _ Hn), app_nth1; [reflexivity|].
      apply Nat.sub_lt; [assumption|apply Nat.lt_0_succ].
- 
assumption.
Qed.

  (**  An alternative tail-recursive definition for reverse *)

  Fixpoint rev_append (l l': list A) : list A :=
    match l with
      | [] => l'
      | a::l => rev_append l (a::l')
    end.

  Definition rev' l : list A := rev_append l [].

  Lemma rev_append_rev : forall l l', rev_append l l' = rev l ++ l'.
  Proof. idtac "rev_append_rev".
    Time intro l; induction l ; snipe @app_assoc.
  Qed.

  Lemma rev_alt : forall l, rev l = rev_append l [].
  Proof. idtac "rev_alt".
    Time intros ; snipe (@rev_append_rev, @app_nil_r).
  Qed.

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Fixpoint concat (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x l => x ++ concat l
  end.

  Lemma concat_nil : concat nil = nil.
  Proof. idtac "concat_nil".
  Time snipe.
  Qed.

  Lemma concat_cons : forall x l, concat (cons x l) = x ++ concat l.
  Proof. idtac "concat_cons".
  Time snipe.
  Qed.

  Lemma concat_app : forall l1 l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
  Proof. idtac "concat_app".
  Time intros l1; induction l1 ; snipe @app_assoc.
  Qed.

  Lemma in_concat : forall l y,
    In y (concat l) <-> exists x, In x l /\ In y x.
  Proof. idtac "in_concat".
    intro l; induction l as [|a l IHl]; simpl; intro y; split; intros H.
    contradiction.
    destruct H as (x,(H,_)); contradiction.
    destruct (in_app_or _ _ _ H) as [H0|H0].
    exists a; auto.
    destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
    exists x; auto.
    apply in_or_app.
    destruct H as (x,(H0,H1)); destruct H0.
    subst; auto.
    right; destruct (IHl y) as (_,H2); apply H2.
    exists x; auto.
  Qed.


  (***********************************)
  (** ** Decidable equality on lists *)
  (***********************************)

  Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.

  Lemma list_eq_dec : forall l l':list A, {l = l'} + {l <> l'}.
  Proof. idtac "list_eq_dec". decide equality. Qed.

  Lemma count_occ_rev l x : count_occ eq_dec (rev l) x = count_occ eq_dec l x.
  Proof. idtac "count_occ_rev".
    induction l as [|a l IHl]; trivial.
    cbn; rewrite count_occ_app, IHl; cbn.
    destruct (eq_dec a x); rewrite Nat.add_comm; reflexivity.
  Qed.

End ListOps.

(***************************************************)
(** * Applying functions to the elements of a list *)
(***************************************************)

(************)
(** ** Map  *)
(************)

Section Map.
  Variables (A : Type) (B : Type).
  Variables (HA : CompDec A) (HB : CompDec B).
  Variable f : A -> B.

  Fixpoint map (l:list A) : list B :=
    match l with
      | [] => []
      | a :: t => (f a) :: (map t)
    end.

  Lemma map_cons (x:A)(l:list A) : map (x::l) = (f x) :: (map l).
  Proof. idtac "map_cons".
   Time snipe.
  Qed.

  Lemma in_map :
    forall (l:list A) (x:A), Inb x l -> Inb (f x) (map l).
  Proof. idtac "in_map".
  Time  intro l; induction l; snipe.
  Qed.

  Lemma in_map_iff : forall l y, In y (map l) <-> exists x, f x = y /\ In x l.
  Proof. idtac "in_map_iff".
    intro l; induction l; firstorder (subst; auto).
  Qed.

  Lemma map_length : forall l, length (map l) = length l.
  Proof. idtac "map_length".
    Time intro l; induction l; snipe.
  Qed.

  Lemma map_nth : forall l d n,
    nth n (map l) (f d) = f (nth n l d).
  Proof. idtac "map_nth".
   intro l; induction l; simpl map; intros d n; destruct n; firstorder.
  Qed.

  Lemma nth_error_map : forall n l,
    nth_error (map l) n = option_map f (nth_error l n).
  Proof. idtac "nth_error_map".
    intro n. induction n as [|n IHn]; intro l.
    - now destruct l.
    - destruct l as [|? l]; [reflexivity|exact (IHn l)].
  Qed.

  Lemma map_nth_error : forall n l d,
    nth_error l n = Some d -> nth_error (map l) n = Some (f d).
  Proof. idtac "map_nth_error".
    intros n l d H. now rewrite nth_error_map, H.
  Qed.

  Lemma map_app : forall l l',
    map (l++l') = (map l)++(map l').
  Proof. idtac "map_app".
   Time intro l ; induction l ; snipe.
  Qed.

  Lemma map_last : forall l a,
    map (l ++ [a]) = (map l) ++ [f a].
  Proof. idtac "map_last".
    Time intro l; induction l ; snipe.
  Qed.

  Lemma map_rev : forall l, map (rev l) = rev (map l).
  Proof. idtac "map_rev".
    Time intro l; induction l ; snipe @map_app.
  Qed.

  Lemma map_eq_nil : forall l, map l = [] -> l = [].
  Proof. idtac "map_eq_nil".
    intro l; destruct l; simpl; reflexivity || discriminate.
  Qed.

  Lemma map_eq_cons : forall l l' b,
    map l = b :: l' -> exists a tl, l = a :: tl /\ f a = b /\ map tl = l'.
  Proof. idtac "map_eq_cons".
    intros l l' b Heq.
    destruct l as [|a l]; inversion_clear Heq.
    exists a, l; repeat split.
  Qed.

  Lemma map_eq_app  : forall l l1 l2,
    map l = l1 ++ l2 -> exists l1' l2', l = l1' ++ l2' /\ map l1' = l1 /\ map l2' = l2.
  Proof. idtac "map_eq_app ".
    intro l; induction l as [|a l IHl]; simpl; intros l1 l2 Heq.
    - symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; subst.
      exists nil, nil; repeat split.
    assumption.
    - destruct l1; simpl in Heq; inversion Heq as [[Heq2 Htl]].
      + exists nil, (a :: l); repeat split.
      + destruct (IHl _ _ Htl) as (l1' & l2' & ? & ? & ?); subst.
        exists (a :: l1'), l2'; repeat split.
  Qed.

  (** [map] and count of occurrences *)

  Hypothesis decA: forall x1 x2 : A, {x1 = x2} + {x1 <> x2}.
  Hypothesis decB: forall y1 y2 : B, {y1 = y2} + {y1 <> y2}.

  Hypothesis Hfinjective: forall x1 x2: A, (f x1) = (f x2) -> x1 = x2.

  Theorem count_occ_map x l:
    count_occ decA l x = count_occ decB (map l) (f x).
  Proof. idtac "count_occ_map".
   revert x.
 induction l as [| a l' Hrec]; intro x; simpl.
    - reflexivity.
    - specialize (Hrec x).
      destruct (decA a x) as [H1|H1], (decB (f a) (f x)) as [H2|H2].
      + rewrite Hrec. reflexivity.
      + contradiction H2. rewrite H1. reflexivity.
      + specialize (Hfinjective H2). contradiction H1.
      + assumption.
  Qed.

End Map.

(*****************)
(** ** Flat Map  *)
(*****************)

Section FlatMap.
  Variables (A : Type) (B : Type).
  Variables (HA : CompDec A) (HB : CompDec B).
  Variable f : A -> list B.

    (** [flat_map] *)

    Definition flat_map :=
      fix flat_map (l:list A) : list B :=
      match l with
        | nil => nil
        | cons x t => (f x)++(flat_map t)
      end.

    Lemma flat_map_concat_map l :
      flat_map l = concat (map f l).
    Proof. idtac "flat_map_concat_map".
      induction l as [|x l IH]; simpl.
      - reflexivity.
      - rewrite IH; reflexivity.
    Qed.

    Lemma flat_map_app l1 l2 :
      flat_map (l1 ++ l2) = flat_map l1 ++ flat_map l2.
    Proof. idtac "flat_map_app".
     rewrite !flat_map_concat_map, map_app, concat_app. reflexivity.
    assumption. assumption. apply SMT_classes_instances.list_compdec.
    Qed.

    Lemma in_flat_map l y :
      In y (flat_map l) <-> exists x, In x l /\ In y (f x).
    Proof. idtac "in_flat_map".
      rewrite flat_map_concat_map, in_concat.
      split.
      - intros [l' [[x [<- ?]] %in_map_iff ?]].
        now exists x.
      - intros [x [? ?]]. exists (f x).
       now split; [apply List.in_map|].
    Qed.

End FlatMap.


Lemma concat_map : forall A B (f : A -> B) (HA : CompDec A) 
(HB : CompDec B) l, map f (concat l) = concat (map (map f) l).
Proof. idtac "concat_map".
  intros A B HA HB f l; induction l as [|x l IH]; simpl.
  - reflexivity.
  - rewrite map_app, IH. reflexivity. assumption. assumption.
Qed.

Lemma remove_concat A (eq_dec : forall x y : A, {x = y}+{x <> y}) : forall l x,
  remove eq_dec x (concat l) = flat_map (remove eq_dec x) l.
Proof. idtac "remove_concat".
  intros l x; induction l as [|? ? IHl]; [ reflexivity | simpl ].
  rewrite List.remove_app, IHl; reflexivity.
Qed.

Lemma map_id : forall (A :Type) (l : list A),
  map (fun x => x) l = l.
Proof. idtac "map_id".
  intros A l; induction l as [|? ? IHl]; simpl; auto; rewrite IHl; auto.
Qed.

Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
  map g (map f l) = map (fun x => g (f x)) l.
Proof. idtac "map_map".
  intros A B C f g l; induction l as [|? ? IHl]; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma map_ext_in :
  forall (A B : Type)(f g:A->B) l, (forall a, In a l -> f a = g a) -> map f l = map g l.
Proof. idtac "map_ext_in".
  intros A B f g l; induction l as [|? ? IHl]; simpl; auto.
  intros H; rewrite H by intuition; rewrite IHl; auto.
Qed.

Lemma ext_in_map :
  forall (A B : Type)(f g:A->B) l, map f l = map g l -> forall a, In a l -> f a = g a.
Proof. idtac "ext_in_map". intros A B f g l; induction l; intros [=] ? []; subst; auto. Qed.

Arguments ext_in_map [A B f g l].

Lemma map_ext_in_iff :
   forall (A B : Type)(f g:A->B) l, map f l = map g l <-> forall a, In a l -> f a = g a.
Proof. idtac "map_ext_in_iff". split; [apply ext_in_map | apply map_ext_in]. Qed.

Arguments map_ext_in_iff {A B f g l}.

Lemma map_ext :
  forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, map f l = map g l.
Proof. idtac "map_ext".
  intros; apply map_ext_in; auto.
Qed.

Lemma flat_map_ext : forall (A B : Type)(f g : A -> list B),
  (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
Proof. idtac "flat_map_ext".
  intros A B f g Hext l.
  rewrite 2 flat_map_concat_map.
  now rewrite (map_ext _ g).
Qed.

Lemma nth_nth_nth_map A : forall (l : list A) (HA : CompDec A) n d ln dn, n < length ln \/ length l <= dn ->
  nth (nth n ln dn) l d = nth n (map (fun x => nth x l d) ln) d.
Proof. idtac "nth_nth_nth_map".
  intros l HA n d ln dn Hlen.
  rewrite <- (map_nth (fun m => nth m l d)).
  destruct Hlen.
  - apply nth_indep. rewrite map_length. assumption. apply SMT_classes_instances.Nat_compdec.
assumption.
  - now rewrite (nth_overflow l).
Qed.



(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type) (HA : CompDec A) (HB : CompDec B).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l:list B) (a0:A) : A :=
    match l with
      | nil => a0
      | cons b t => fold_left t (f a0 b)
    end.

  Lemma fold_left_app : forall (l l':list B)(i:A),
    fold_left (l++l') i = fold_left l' (fold_left l i).
  Proof. idtac "fold_left_app".
    Time intro l ; induction l ; snipe.
  Qed.

End Fold_Left_Recursor.

Lemma fold_left_length :
  forall (A:Type)(l:list A) (HA: CompDec A), fold_left (fun x _ => S x) l 0 = length l.
Proof. idtac "fold_left_length".
intros A l HA. induction l as [ |? ? IH] using List.rev_ind; [reflexivity|].
  rewrite fold_left_app, app_length, IH, Nat.add_comm. simpl. reflexivity. 
assumption. apply SMT_classes_instances.Nat_compdec. assumption.
Qed.

(************************************)
(** Right-to-left iterator on lists *)
(************************************)

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variables (HA : CompDec A) (HB : CompDec B).
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_right (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right t)
    end.

End Fold_Right_Recursor.

  Lemma fold_right_app : forall (A B:Type)(f:A->B->B) l l' i,
    fold_right f i (l++l') = fold_right f (fold_right f i l') l.
  Proof. idtac "fold_right_app".
    intros A B f l; induction l.
    simpl; auto.
    simpl; intros.
    f_equal; auto.
  Qed.

  Lemma fold_left_rev_right : forall (A B:Type)(f:A->B->B) l i,
    fold_right f i (rev l) = fold_left (fun x y => f y x) l i.
  Proof. idtac "fold_left_rev_right".
    intros A B f l; induction l.
    simpl; auto.
    intros.
    simpl.
    rewrite fold_right_app; simpl; auto.
 Qed.

  Theorem fold_symmetric :
    forall (A : Type) (f : A -> A -> A),
    (forall x y z : A, f x (f y z) = f (f x y) z) ->
    forall (a0 : A), (forall y : A, f a0 y = f y a0) ->
    forall (l : list A), fold_left f l a0 = fold_right f a0 l.
  Proof. idtac "fold_symmetric".
    intros A f assoc a0 comma0 l.
    induction l as [ | a1 l IHl]; [ simpl; reflexivity | ].
    simpl. rewrite <- IHl. clear IHl. revert a1.
    induction l as [|? ? IHl]; [ auto | ].
    simpl. intro. rewrite <- assoc. rewrite IHl. rewrite IHl. auto.
  Qed.

  (** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
      indexed by elts of [x], sorted in lexicographic order. *)

  Fixpoint list_power (A B:Type)(l:list A) (l':list B) :
    list (list (A * B)) :=
    match l with
      | nil => cons nil nil
      | cons x t =>
	flat_map (fun f:list (A * B) => map (fun y:B => cons (x, y) f) l')
        (list_power t l')
    end.


  (*************************************)
  (** ** Boolean operations over lists *)
  (*************************************)

  Section Bool.
    Variable A : Type.
    Variable (HA : CompDec A).
    Variable f : A -> bool.

  (** find whether a boolean function can be satisfied by an
       elements of the list. *)

    Fixpoint existsb (l:list A) : bool :=
      match l with
      | nil => false
      | a::l => f a || existsb l
      end.

    Lemma existsb_exists :
      forall l, existsb l = true <-> exists x, In x l /\ f x.
    Proof. idtac "existsb_exists".
      intro l; induction l as [ | a m IH ]; split; simpl.
      - easy.
      - intros [x [[]]].
      - destruct (f a) eqn:Ha.
        + intros _. exists a. tauto.
        + intros [x [? ?]] %IH. exists x. tauto.
      - intros [ x [ [ Hax | Hxm ] Hfx ] ].
        + now rewrite Hax, Hfx.
        + destruct IH as [ _ -> ]; eauto with bool.
    Qed.

    Lemma existsb_nth : forall l n d, n < length l ->
      existsb l = false -> f (nth n l d) = false.
    Proof. idtac "existsb_nth".
     intro l; induction l as [|a ? IHl]; [easy|].
      cbn. intros [|n]; [now destruct (f a)|].
      intros d ? %Nat.succ_lt_mono.
      now destruct (f a); [|apply IHl].
    Qed.

    Lemma existsb_app : forall l1 l2,
      existsb (l1++l2) = existsb l1 || existsb l2.
    Proof. idtac "existsb_app".
     Time intro l1; induction l1 ; snipe.
    Qed.

  (** find whether a boolean function is satisfied by
    all the elements of a list. *)

    Fixpoint forallb (l:list A) : bool :=
      match l with
      | nil => true
      | a::l => f a && forallb l
      end.

    Lemma forallb_forall :
      forall l, forallb l = true <-> (forall x, In x l -> f x = true).
    Proof. idtac "forallb_forall".
         intro l; induction l as [|a l IHl]; simpl; [ tauto | split; intro H ].
      + destruct (andb_prop _ _ H); intros a' [?|?].
        - congruence.
        - apply IHl; assumption.
      + apply andb_true_intro; split.
        - apply H; left; reflexivity.
        - apply IHl; intros; apply H; right; assumption.
    Qed.

    Lemma forallb_app :
      forall l1 l2, forallb (l1++l2) = forallb l1 && forallb l2.
    Proof. idtac "forallb_app".
      intro l1; induction l1 as [|a ? ?]; simpl.
        solve[auto].
      case (f a); simpl; solve[auto].
    Qed.

  (** [filter] *)

    Fixpoint filter (l:list A) : list A :=
      match l with
      | nil => nil
      | x :: l => if f x then x::(filter l) else filter l
      end.

    Lemma filter_In : forall x l, In x (filter l) <-> In x l /\ f x = true.
    Proof. idtac "filter_In".
      intros x l; induction l as [|a ? ?]; simpl.
      - tauto.
      - intros.
        case_eq (f a); intros; simpl; intuition congruence.
    Qed.

    Lemma filter_app (l l':list A) :
      filter (l ++ l') = filter l ++ filter l'.
    Proof. idtac "filter_app".
      induction l as [|x l IH]; simpl; trivial.
      destruct (f x); simpl; now rewrite IH.
    Qed.

    Lemma concat_filter_map : forall (l : list (list A)),
      concat (map filter l) = filter (concat l).
    Proof. idtac "concat_filter_map".
      intro l; induction l as [| v l IHl]; [auto|].
      simpl. rewrite IHl. rewrite filter_app. reflexivity.
    Qed.

  (** [find] *)

    Fixpoint find (l:list A) : option A :=
      match l with
      | nil => None
      | x :: tl => if f x then Some x else find tl
      end.

    Lemma find_some l x : find l = Some x -> In x l /\ f x = true.
    Proof. idtac "find_some".
     induction l as [|a l IH]; simpl; [easy| ].
     case_eq (f a); intros Ha Eq.
     * injection Eq as [= ->]; auto.
     * destruct (IH Eq); auto.
    Qed.

    Lemma find_none l : find l = None -> forall x, In x l -> f x = false.
    Proof. idtac "find_none".
     induction l as [|a l IH]; simpl; [easy|].
     case_eq (f a); intros Ha Eq x IN; [easy|].
     destruct IN as [<-|IN]; auto.
    Qed.

  (** [partition] *)

 
    Fixpoint partition (l:list A) : list A * list A :=
      match l with
      | nil => (nil, nil)
      | x :: tl => let (g,d) := partition tl in
                   if f x then (x::g,d) else (g,x::d)
      end.

  Theorem partition_cons1 a l l1 l2:
    partition l = (l1, l2) ->
    f a = true ->
    partition (a::l) = (a::l1, l2).
  Proof. idtac "partition_cons1".
    simpl. now intros -> ->.
  Qed.

  Theorem partition_cons2 a l l1 l2:
    partition l = (l1, l2) ->
    f a=false ->
    partition (a::l) = (l1, a::l2).
  Proof. idtac "partition_cons2".
    simpl. now intros -> ->.
  Qed.

  Theorem partition_length l l1 l2:
    partition l = (l1, l2) ->
    length l = length l1 + length l2.
  Proof. idtac "partition_length".
    revert l1 l2. induction l as [ | a l' Hrec]; intros l1 l2.
    - now intros [= <- <- ].
    - simpl. destruct (f a), (partition l') as (left, right);
      intros [= <- <- ]; simpl; rewrite (Hrec left right); auto.
  Qed.

  Theorem partition_inv_nil (l : list A):
    partition l = ([], []) <-> l = [].
  Proof. idtac "partition_inv_nil".
    split.
    - destruct l as [|a l'].
      * intuition.
      * simpl. destruct (f a), (partition l'); now intros [= -> ->].
    - now intros ->.
  Qed.

  Theorem elements_in_partition l l1 l2:
    partition l = (l1, l2) ->
    forall x:A, In x l <-> In x l1 \/ In x l2.
  Proof. idtac "elements_in_partition".
    revert l1 l2. induction l as [| a l' Hrec]; simpl; intros l1 l2 Eq x.
    - injection Eq as [= <- <-]. tauto.
    - destruct (partition l') as (left, right).
      specialize (Hrec left right eq_refl x).
      destruct (f a); injection Eq as [= <- <-]; simpl; tauto.
  Qed.

  End Bool.


  (*******************************)
  (** ** Further filtering facts *)
  (*******************************)

    (*******************************)
  (** ** Further filtering facts *)
  (*******************************)

  Section Filtering.
    Variables (A : Type).

    Lemma filter_ext_in : forall (f g : A -> bool) (l : list A),
      (forall a, In a l -> f a = g a) -> filter f l = filter g l.
    Proof. idtac "filter_ext_in".
      intros f g l. induction l as [| a l IHl]; [easy|cbn].
      intros H. rewrite (H a) by (now left).
      destruct (g a); [f_equal|]; apply IHl; intros; apply H; now right.
    Qed.

    Lemma ext_in_filter : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l -> (forall a, In a l -> f a = g a).
    Proof. idtac "ext_in_filter".
      intros f g l. induction l as [| a l IHl]; [easy|cbn].
      intros H. assert (Ha : f a = g a).
      - pose proof (Hf := proj1 (filter_In f a l)).
        pose proof (Hg := proj1 (filter_In g a l)).
        destruct (f a), (g a); [reflexivity| | |reflexivity].
        + symmetry. apply Hg. rewrite <- H. now left.
        + apply Hf. rewrite H. now left.
      - intros b [<-|Hbl]; [assumption|].
        apply IHl; [|assumption].
        destruct (f a), (g a); congruence.
    Qed.

    Lemma filter_ext_in_iff : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l <-> (forall a, In a l -> f a = g a).
    Proof. idtac "filter_ext_in_iff".
      split; [apply ext_in_filter | apply filter_ext_in].
    Qed.

    Lemma filter_map : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l <-> map f l = map g l.
    Proof. idtac "filter_map".
      intros f g l. now rewrite filter_ext_in_iff, map_ext_in_iff.
    Qed.

    Lemma filter_ext : forall (f g : A -> bool),
      (forall a, f a = g a) -> forall l, filter f l = filter g l.
    Proof. idtac "filter_ext".
      intros f g H l. rewrite filter_map. apply map_ext. assumption.
    Qed.

    (** Remove by filtering *)

    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

    Definition remove' (x : A) : list A -> list A :=
      filter (fun y => if eq_dec x y then false else true).

    Lemma remove_alt (x : A) (l : list A) : remove' x l = remove eq_dec x l.
    Proof. idtac "remove_alt".
      induction l; [reflexivity|].
      simpl. now destruct eq_dec; [|f_equal].
    Qed.

    (** Counting occurrences by filtering *)

    Definition count_occ' (l : list A) (x : A) : nat :=
      length (filter (fun y => if eq_dec y x then true else false) l).

    Lemma count_occ_alt (l : list A) (x : A) :
      count_occ' l x = count_occ eq_dec l x.
    Proof. idtac "count_occ_alt".
    unfold count_occ'. induction l; [reflexivity|].
      simpl. now destruct eq_dec; simpl; [f_equal|].
    Qed.

  End Filtering.


  (******************************************************)
  (** ** Operations on lists of pairs or lists of lists *)
  (******************************************************)

  Section ListPairs.
    Variables (A : Type) (B : Type).

  (** [split] derives two lists from a list of pairs *)

    Fixpoint split (l:list (A*B)) : list A * list B :=
      match l with
      | [] => ([], [])
      | (x,y) :: tl => let (left,right) := split tl in (x::left, y::right)
      end.

    Lemma in_split_l : forall (l:list (A*B))(p:A*B),
      In p l -> In (fst p) (fst (split l)).
    Proof. idtac "in_split_l".
      intro l. induction l as [|[? ?] l IHl]; [easy|].
      intros [? ?]. cbn.
      now intros [[=]|? %IHl]; destruct (split l); [left|right].
    Qed.

    Lemma in_split_r : forall (l:list (A*B))(p:A*B),
      In p l -> In (snd p) (snd (split l)).
    Proof. idtac "in_split_r".
      intro l. induction l as [|[? ?] l IHl]; [easy|].
      intros [? ?]. cbn.
      now intros [[=]|? %IHl]; destruct (split l); [left|right].
    Qed.

    Lemma split_nth : forall (l:list (A*B))(n:nat)(d:A*B),
      nth n l d = (nth n (fst (split l)) (fst d), nth n (snd (split l)) (snd d)).
    Proof. idtac "split_nth".
      intro l; induction l as [|a l IHl].
      intros n d; destruct n; destruct d; simpl; auto.
      intros n d; destruct n; destruct d; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
      destruct a; destruct (split l); simpl in *; auto.
      apply IHl.
    Qed.

    Lemma split_length_l : forall (l:list (A*B)),
      length (fst (split l)) = length l.
    Proof. idtac "split_length_l".
      intro l; induction l as [|a l IHl]; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

    Lemma split_length_r : forall (l:list (A*B)),
      length (snd (split l)) = length l.
    Proof. idtac "split_length_r".
      intro l; induction l as [|a l IHl]; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

  (** [combine] is the opposite of [split].
      Lists given to [combine] are meant to be of same length.
      If not, [combine] stops on the shorter list *)

    Fixpoint combine (l : list A) (l' : list B) : list (A*B) :=
      match l,l' with
      | x::tl, y::tl' => (x,y)::(combine tl tl')
      | _, _ => nil
      end.

    Lemma split_combine : forall (l: list (A*B)),
      forall l1 l2, split l = (l1, l2) -> combine l1 l2 = l.
    Proof. idtac "split_combine".
      intro l; induction l as [|a l IHl].
      simpl; auto.
      all: intuition; inversion H; auto.
      destruct (split l); simpl in *.
      inversion H1; subst; simpl.
      f_equal; auto.
    Qed.

    Lemma combine_split : forall (l:list A)(l':list B), length l = length l' ->
      split (combine l l') = (l,l').
    Proof. idtac "combine_split".
      intro l; induction l as [|a l IHl]; intro l'; destruct l';
       simpl; trivial; try discriminate.
      now intros [= ->%IHl].
    Qed.

    Lemma in_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In x l.
    Proof. idtac "in_combine_l".
      intro l; induction l as [|a l IHl].
      simpl; auto.
      intro l'; destruct l' as [|a0 l']; simpl; auto; intros x y H.
      destruct H. inversion H. auto. apply IHl in H. auto.
    Qed.

    Lemma in_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In y l'.
    Proof. idtac "in_combine_r".
      intro l; induction l as [|? ? IHl].
      simpl; intros; contradiction.
      intro l'; destruct l'; simpl; auto; intros x y H.
      destruct H as [H|H].
      injection H; auto.
      right; apply IHl with x; auto.
    Qed.

    Lemma combine_length : forall (l:list A)(l':list B),
      length (combine l l') = min (length l) (length l').
    Proof. idtac "combine_length".
      intro l; induction l.
      simpl; auto.
      intro l'; destruct l'; simpl; auto.
    Qed.

    Lemma combine_nth : forall (l:list A)(l':list B)(n:nat)(x:A)(y:B),
      length l = length l' ->
      nth n (combine l l') (x,y) = (nth n l x, nth n l' y).
    Proof. idtac "combine_nth".
      intro l; induction l; intro l'; destruct l'; intros n x y; try discriminate.
      destruct n; simpl; auto.
      destruct n; simpl in *; auto.
    Qed.

  (** [list_prod] has the same signature as [combine], but unlike
     [combine], it adds every possible pairs, not only those at the
     same position. *)

    Fixpoint list_prod (l:list A) (l':list B) :
      list (A * B) :=
      match l with
      | nil => nil
      | cons x t => (map (fun y:B => (x, y)) l')++(list_prod t l')
      end.

    Lemma in_prod_aux :
      forall (x:A) (y:B) (l:list B),
	In y l -> In (x, y) (map (fun y0:B => (x, y0)) l).
    Proof. idtac "in_prod_aux".
      intros x y l; induction l;
	[ simpl; auto
	  | simpl; destruct 1 as [H1| ];
	    [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma in_prod :
      forall (l:list A) (l':list B) (x:A) (y:B),
        In x l -> In y l' -> In (x, y) (list_prod l l').
    Proof. idtac "in_prod".
      intro l; induction l;
      [ simpl; tauto
        | simpl; intros l' x y H H0; apply in_or_app; destruct H as [H|H];
          [ left; rewrite H; apply in_prod_aux; assumption | right; auto ] ].
  eapply IHl in H. eauto. assumption.
    Qed.

    Lemma in_prod_iff :
      forall (l:list A)(l':list B)(x:A)(y:B),
        In (x,y) (list_prod l l') <-> In x l /\ In y l'.
    Proof. idtac "in_prod_iff".
      intros l l' x y; split; [ | intros H; now apply in_prod ].
      induction l as [|a l IHl]; cbn; [easy|].
      intros [[? [[= -> ->] ?]] %in_map_iff|] %in_app_or; tauto.
    Qed.

    Lemma prod_length : forall (l:list A)(l':list B) (HA : CompDec A) (HB : CompDec B),
      length (list_prod l l') = (length l) * (length l').
    Proof. idtac "prod_length".
      intro l; induction l as [|? ? IHl]; simpl; [easy|].
      intros. rewrite app_length, map_length, IHl. reflexivity.
    all: try assumption. all: apply SMT_classes_instances.prod_compdec.
    Qed.

  End ListPairs.
 

(*****************************************)
(** * Miscellaneous operations on lists  *)
(*****************************************)



(******************************)
(** ** Length order of lists  *)
(******************************)

Section length_order.
  Variable A : Type.
  Variable HA : CompDec A.

  Definition lel (l m:list A) := length l <=? length m.
  (* Note : trakt fail when lel is not boolean *)

  Variables a b : A.
  Variables l m n : list A.

  Lemma lel_refl : lel l l.
  Proof. idtac "lel_refl".
  Time snipe.
  Qed.

  Lemma lel_trans : lel l m -> lel m n -> lel l n.
  Proof. idtac "lel_trans".
  Time snipe. Qed.

  Lemma lel_cons_cons : lel l m -> lel (a :: l) (b :: m).
  Proof. idtac "lel_cons_cons". 
  Time snipe. Qed.

  Lemma lel_cons : lel l m -> lel l (b :: m).
  Proof. idtac "lel_cons".
  Time snipe. Qed.

 Lemma lel_tail : lel (a :: l) (b :: m) -> lel l m.
  Proof. idtac "lel_tail".
    intros. unfold lel in H. simpl in H. auto.
  Qed.

  Lemma lel_nil : forall l':list A, lel l' nil -> nil = l'.
  Proof. idtac "lel_nil".
    intro l'; elim l'; [now intros|].
    intros a0 l0 H H1. unfold lel in H1. simpl in H1. 
discriminate H1.
  Qed.
End length_order.


#[global]
Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons:
  datatypes.

#[global]
Hint Resolve app_assoc app_assoc_reverse: datatypes.
#[global]
Hint Resolve app_comm_cons app_cons_not_nil: datatypes.
#[global]
Hint Immediate app_eq_nil: datatypes.
#[global]
Hint Resolve app_eq_unit app_inj_tail: datatypes.
#[global]
Hint Resolve in_eq in_cons in_inv in_nil in_app_or in_or_app: datatypes.

(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.


  Variable A : Type.
  Variable HA : CompDec A.

  Definition incl (l m:list A) := forall a:A, In a l -> In a m.
  #[local]
  Hint Unfold incl : core.

  Lemma incl_nil_l : forall l, incl nil l.
  Proof. idtac "incl_nil_l".
    intros l a Hin; inversion Hin.
  Qed.

  Lemma incl_l_nil : forall l, incl l nil -> l = nil.
  Proof. idtac "incl_l_nil".
    intro l; destruct l as [|a l]; intros Hincl.
    - reflexivity.
    - exfalso; apply Hincl with a; simpl; auto.
  Qed.

  Lemma incl_refl : forall l:list A, incl l l.
  Proof. idtac "incl_refl".
    auto.
  Qed.
  #[local]
  Hint Resolve incl_refl : core.

  Lemma incl_tl : forall (a:A) (l m:list A), incl l m -> incl l (a :: m).
  Proof. idtac "incl_tl".
  exact (fun (a : A) (l m : list A) (H : incl l m) (a0 : A) (H0 : In a0 l) =>
in_cons a a0 m (H a0 H0)).
  Qed.
  #[local]
  Hint Immediate incl_tl : core.

  Lemma incl_tran : forall l m n:list A, incl l m -> incl m n -> incl l n.
  Proof. idtac "incl_tran".
    auto.
  Qed.

  Lemma incl_appl : forall l m n:list A, incl l n -> incl l (n ++ m).
  Proof. idtac "incl_appl".
    exact (fun (l m n : list A) (H : incl l n) (a : A) (H0 : In a l) =>
in_or_app n m a (or_introl (H a H0))).
  Qed.
  #[local]
  Hint Immediate incl_appl : core.

  Lemma incl_appr : forall (l m n: list A )(HA : CompDec A), incl l n -> incl l (m ++ n).
  Proof. idtac "incl_appr".
  unfold incl. intros; apply in_or_app. right. apply H. auto.
  Qed.
  #[local]
  Hint Immediate incl_appr : core.

  Lemma incl_cons :
    forall (a:A) (l m:list A), In a m -> incl l m -> incl (a :: l) m.
  Proof. idtac "incl_cons".
    now intros a l m ? H b [<-|]; [|apply H].
  Qed.
  #[local]
  Hint Resolve incl_cons : core.

  Lemma incl_cons_inv : forall (a:A) (l m:list A),
    incl (a :: l) m -> In a m /\ incl l m.
  Proof. idtac "incl_cons_inv".
    intros a l m Hi.
    split; [ | intros ? ? ]; apply Hi; simpl; auto.
  Qed.

  Lemma incl_app : forall l m n:list A, incl l n -> incl m n -> incl (l ++ m) n.
  Proof. idtac "incl_app".
    unfold incl; simpl; intros l m n H H0 a H1.
    now_show (In a n).
    elim (in_app_or _ _ _ H1); auto.
  Qed.
  #[local]
  Hint Resolve incl_app : core.

  Lemma incl_app_app : forall l1 l2 m1 m2:list A,
    incl l1 m1 -> incl l2 m2 -> incl (l1 ++ l2) (m1 ++ m2).
  Proof. idtac "incl_app_app".
    intros.
    apply incl_app; [ apply incl_appl | apply incl_appr]; assumption.
  Qed.

  Lemma incl_app_inv : forall l1 l2 m : list A,
    incl (l1 ++ l2) m -> incl l1 m /\ incl l2 m.
  Proof. idtac "incl_app_inv".
    intro l1; induction l1 as [|a l1 IHl1]; intros l2 m Hin; split; auto.
    - apply incl_nil_l.
    - intros b Hb; inversion_clear Hb; subst; apply Hin.
      + now constructor.
      + simpl; apply in_cons.
        apply incl_appl with l1; [ apply incl_refl | assumption ].
    - apply IHl1.
      now apply incl_cons_inv in Hin.
  Qed.

  Lemma incl_filter f l : incl (filter f l) l.
  Proof. idtac "incl_filter". intros x Hin; now apply filter_In in Hin. Qed.

  Lemma remove_incl (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall l1 l2 x,
    incl l1 l2 -> incl (remove eq_dec x l1) (remove eq_dec x l2).
  Proof. idtac "remove_incl".
    intros l1 l2 x Hincl y Hin.
    apply List.in_remove in Hin; destruct Hin as [Hin Hneq].
    apply List.in_in_remove; intuition.
  Qed.

End SetIncl.

Lemma incl_map A B (f : A -> B) l1 l2 : incl l1 l2 -> incl (map f l1) (map f l2).
Proof. idtac "incl_map".
  intros Hincl x Hinx.
  destruct (proj1 (in_map_iff _ _ _) Hinx) as [y [<- Hiny]].
  now apply List.in_map, Hincl.
Qed.


(**************************************)
(** * Cutting a list at some position *)
(**************************************)

Section Cutting.

  Variable A : Type.
  Variable HA : CompDec A.

  Fixpoint firstn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => nil
      | S n => match l with
		 | nil => nil
		 | a::l => a::(firstn n l)
	       end
    end.

  Lemma firstn_nil n: firstn n [] = [].
  Proof. idtac "firstn_nil". Time induction n; snipe. Qed.

  Lemma firstn_cons n a l: firstn (S n) (a::l) = a :: (firstn n l).
  Proof. idtac "firstn_cons". Time snipe. Qed.

  Lemma firstn_all l: firstn (length l) l = l.
  Proof. idtac "firstn_all". induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.

  Lemma firstn_all2 n: forall (l:list A), (length l) <= n -> firstn n l = l.
  Proof. idtac "firstn_all2".
  induction n as [|k iHk].
    - intro l. inversion 1 as [H1|?].
      rewrite (length_zero_iff_nil l) in H1. subst. now simpl.
    - intro l; destruct l as [|x xs]; simpl.
      * now reflexivity.
      * simpl. intro H. f_equal. apply iHk. now apply Nat.succ_le_mono.
  Qed.

  Lemma firstn_O l: firstn 0 l = [].
  Proof. idtac "firstn_O". Time snipe. Qed.

  Lemma firstn_le_length n: forall l:list A, length (firstn n l) <= n.
  Proof. idtac "firstn_le_length".
  Time induction n ; snipe.
  Qed.

  Lemma firstn_length_le: forall l:list A, forall n:nat,
    n <= length l -> length (firstn n l) = n.
  Proof. idtac "firstn_length_le:". intro l; induction l as [|x xs Hrec].
    - simpl. intros n H. apply Nat.le_0_r in H. now subst.
    - intro n; destruct n as [|n].
      * now simpl.
      * simpl. intro H. f_equal. apply Hrec. now apply Nat.succ_le_mono.
  Qed.

  Lemma firstn_app n:
    forall l1 l2,
    firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).
  Proof. idtac "firstn_app".
   induction n as [|k iHk]; intros l1 l2.
    - now simpl.
    - destruct l1 as [|x xs].
      * reflexivity.
      * rewrite <- app_comm_cons. simpl. f_equal. apply iHk. assumption.
  Qed.

  Lemma firstn_app_2 n:
    forall l1 l2,
    firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.
  Proof. idtac "firstn_app_2". induction n as [| k iHk];intros l1 l2.
    - unfold firstn at 2. rewrite Nat.add_0_r, app_nil_r.
      rewrite firstn_app. rewrite Nat.sub_diag.
      unfold firstn at 2. rewrite app_nil_r. apply firstn_all.
    assumption.
    assumption.
    - destruct l2 as [|x xs].
      * simpl. rewrite app_nil_r. apply firstn_all2. now apply Nat.le_add_r. assumption.
      * rewrite firstn_app. assert (H0 : (length l1 + S k - length l1) = S k).
        now rewrite Nat.add_comm, Nat.add_sub.
        rewrite H0, firstn_all2; [reflexivity | now apply Nat.le_add_r].
  Qed.

  Lemma firstn_firstn:
    forall l:list A,
    forall i j : nat,
    firstn i (firstn j l) = firstn (min i j) l.
  Proof. idtac "firstn_firstn:
   ". intro l; induction l as [|x xs Hl].
    - intros. simpl. now rewrite ?firstn_nil.
    - intros [|i]; [easy|].
      intros [|j]; [easy|].
      cbn. f_equal. apply Hl.
  Qed.

  Fixpoint skipn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => l
      | S n => match l with
		 | nil => nil
		 | a::l => skipn n l
	       end
    end.

  Lemma firstn_skipn_comm : forall m n l,
  firstn m (skipn n l) = skipn n (firstn (n + m) l).
  Proof. idtac "firstn_skipn_comm". now intros m n; induction n; intros []; simpl; destruct m. Qed.

  Lemma skipn_firstn_comm : forall m n l,
  skipn m (firstn n l) = firstn (n - m) (skipn m l).
  Proof. idtac "skipn_firstn_comm".  now intro m; induction m; intros [] []; simpl; rewrite ?firstn_nil. Qed.

  Lemma skipn_O : forall l, skipn 0 l = l.
  Proof. idtac "skipn_O". Time snipe. Qed.

  Lemma skipn_nil : forall n, skipn n ([] : list A) = [].
  Proof. idtac "skipn_nil". now intros []. Qed.

  Lemma skipn_cons n a l: skipn (S n) (a::l) = skipn n l.
  Proof. idtac "skipn_cons". Time snipe. Qed.

  Lemma skipn_all : forall l, skipn (length l) l = nil.
  Proof. idtac "skipn_all". now intro l; induction l. Qed.

  Notation skipn_none := skipn_all.

  Lemma skipn_all2 n: forall l, length l <= n -> skipn n l = [].
  Proof. idtac "skipn_all2".
    intros l L%Nat.sub_0_le; rewrite <-(firstn_all l) at 1.
    now rewrite skipn_firstn_comm, L.
  Qed.

  Lemma firstn_skipn : forall n l, firstn n l ++ skipn n l = l.
  Proof. idtac "firstn_skipn".
   Time intro n; induction n; snipe.
  Qed.

  Lemma firstn_length : forall n l, length (firstn n l) = min n (length l).
  Proof. idtac "firstn_length".
  intro n; induction n; intro l; destruct l; simpl; auto.
  Qed.

  Lemma skipn_length n :
    forall l, length (skipn n l) = length l - n.
  Proof. idtac "skipn_length".
    induction n.
    - intros l; simpl; rewrite Nat.sub_0_r; reflexivity.
    - intro l; destruct l; simpl; auto.
  Qed.

  Lemma skipn_app n : forall l1 l2,
    skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
  Proof. idtac "skipn_app". induction n; auto; intros [|]; simpl; auto. Qed.

  Lemma firstn_skipn_rev: forall x l,
      firstn x l = rev (skipn (length l - x) (rev l)).
  Proof. idtac "firstn_skipn_rev:".
    intros x l; rewrite <-(firstn_skipn x l) at 3.
    rewrite rev_app_distr, skipn_app, rev_app_distr, rev_length,
            skipn_length, Nat.sub_diag; simpl. rewrite rev_involutive.
  all: try assumption.
    rewrite <-app_nil_r at 1; f_equal. symmetry; apply length_zero_iff_nil.
   repeat rewrite rev_length, skipn_length. apply Nat.sub_diag. all: assumption.
  Qed.


  Lemma firstn_rev: forall x l,
    firstn x (rev l) = rev (skipn (length l - x) l).
  Proof. idtac "firstn_rev:".
    Time intros x l; snipe (@firstn_skipn_rev, @rev_involutive, @rev_length).
  Qed.

  Lemma skipn_rev: forall x l,
      skipn x (rev l) = rev (firstn (length l - x) l).
  Proof. idtac "skipn_rev:".
    intros x l; rewrite firstn_skipn_rev, rev_involutive, <-rev_length.
    destruct (Nat.le_ge_cases (length (rev l)) x) as [L | L].
    - rewrite skipn_all2; [apply Nat.sub_0_le in L | trivial].
      now rewrite L, Nat.sub_0_r, skipn_all.
    - f_equal. now apply Nat.eq_sym, Nat.add_sub_eq_l, Nat.sub_add.
  - assumption.
  - assumption.
  Qed.
  Lemma removelast_firstn : forall n l, n < length l ->
    removelast (firstn (S n) l) = firstn n l.
  Proof. idtac "removelast_firstn".
    intro n; induction n as [|n IHn]; intros [|? l]; [easy ..|].
    cbn [length firstn]. destruct l.
    - now intros ? %Nat.succ_lt_mono.
    - now intros <- %Nat.succ_lt_mono %IHn.
  Qed.

Definition pred (n: nat) := match n with
| 0 => 0
| S m => m
end.

  Lemma removelast_firstn_len : forall l,
    removelast l = firstn (pred (length l)%nat) l.
  Proof. idtac "removelast_firstn_len".
    intro l; induction l as [|a l IHl]; [ reflexivity | simpl ].
    destruct l; [ | rewrite IHl ]; reflexivity.
  Qed.

  Lemma firstn_removelast : forall n l, n < length l ->
    firstn n (removelast l) = firstn n l.
  Proof. idtac "firstn_removelast".
    intro n; induction n as [|n IHn]; intros [|? l]; [easy ..|].
    cbn [length firstn]. destruct l.
    - now intros ? %Nat.succ_lt_mono.
    - now intros <- %Nat.succ_lt_mono %IHn.
  Qed.

End Cutting.

Section CuttingMap.
  Variables A B : Type.
  Variable f : A -> B.

(** Not handled by snipe: higher-order **)

  Lemma firstn_map : forall n l,
      firstn n (map f l) = map f (firstn n l).
  Proof. idtac "firstn_map".
    intro n; induction n; intros []; simpl; f_equal; trivial.
  Qed.

  Lemma skipn_map : forall n l,
      skipn n (map f l) = map f (skipn n l).
  Proof. idtac "skipn_map".
    intro n; induction n; intros []; simpl; trivial.
  Qed.
End CuttingMap.

(**************************************************************)
(** ** Combining pairs of lists of possibly-different lengths *)
(**************************************************************)

Section Combining.
    Variables (A B : Type).
    Variables (HA : CompDec A) (HB: CompDec B).

    Lemma combine_nil : forall (l : list A),
      combine l (@nil B) = @nil (A*B).
    Proof. idtac "combine_nil".
      intros l.
      apply length_zero_iff_nil.
      rewrite combine_length. simpl. rewrite Nat.min_0_r.
      reflexivity.
    Qed.

    Lemma combine_firstn_l : forall (l : list A) (l' : list B),
      combine l l' = combine l (firstn (length l) l').
    Proof. idtac "combine_firstn_l".
      intro l; induction l as [| x l IHl]; intros l'; [reflexivity|].
      destruct l' as [| x' l']; [reflexivity|].
      simpl. specialize IHl with l'. rewrite <- IHl.
      reflexivity.
    Qed.

    Lemma combine_firstn_r : forall (l : list A) (l' : list B),
      combine l l' = combine (firstn (length l') l) l'.
    Proof. idtac "combine_firstn_r".
      intros l l'. generalize dependent l.
      induction l' as [| x' l' IHl']; intros l.
      - simpl. apply combine_nil.
      - destruct l as [| x l]; [reflexivity|].
        simpl. specialize IHl' with l. rewrite <- IHl'.
        reflexivity.
    Qed.

    Lemma combine_firstn : forall (l : list A) (l' : list B) (n : nat),
      firstn n (combine l l') = combine (firstn n l) (firstn n l').
    Proof. idtac "combine_firstn".
      intro l; induction l as [| x l IHl]; intros l' n.
      - simpl. repeat (rewrite firstn_nil). reflexivity.
      assumption. apply SMT_classes_instances.prod_compdec.
      - destruct l' as [| x' l'].
        + simpl. repeat (rewrite firstn_nil).
        simpl. destruct n as [| n]; [reflexivity|].
          repeat (rewrite firstn_cons). simpl. reflexivity.
        assumption.
        assumption. apply SMT_classes_instances.prod_compdec.
        + simpl. destruct n. simpl. reflexivity. simpl. rewrite IHl.
auto.
    Qed.

End Combining.

(**********************************************************************)
(** ** Predicate for List addition/removal (no need for decidability) *)
(**********************************************************************)

Section Add.

  Variable A : Type.
  Variable HA : CompDec A.

(** Inductive Predicate : not handled by snipe **)

  (* [Add a l l'] means that [l'] is exactly [l], with [a] added
     once somewhere *)
  Inductive Add (a:A) : list A -> list A -> Prop :=
    | Add_head l : Add a l (a::l)
    | Add_cons x l l' : Add a l l' -> Add a (x::l) (x::l').

  Lemma Add_app a l1 l2 : Add a (l1++l2) (l1++a::l2).
  Proof. idtac "Add_app".
   induction l1; simpl; now constructor.
  Qed.

  Lemma Add_split a l l' :
    Add a l l' -> exists l1 l2, l = l1++l2 /\ l' = l1++a::l2.
  Proof. idtac "Add_split".
   induction 1 as [l|x ? ? ? IHAdd].
   - exists nil; exists l; split; trivial.
   - destruct IHAdd as (l1 & l2 & Hl & Hl').
     exists (x::l1); exists l2; split; simpl; f_equal; trivial.
  Qed.

  Lemma Add_in a l l' : Add a l l' ->
   forall x, In x l' <-> In x (a::l).
  Proof. idtac "Add_in".
   induction 1 as [|? ? ? ? IHAdd]; intros; simpl in *; rewrite ?IHAdd; tauto.
  Qed.

  Lemma Add_length a l l' : Add a l l' -> length l' = S (length l).
  Proof. idtac "Add_length".
   induction 1; simpl; now auto.
  Qed.

  Lemma Add_inv a l : In a l -> exists l', Add a l' l.
  Proof. idtac "Add_inv".
   intro Ha. destruct (in_split _ _ Ha) as (l1 & l2 & ->).
   exists (l1 ++ l2). apply Add_app.
  Qed.

  Lemma incl_Add_inv a l u v :
    ~In a l -> incl (a::l) v -> Add a u v -> incl l u.
  Proof. idtac "incl_Add_inv".
  intros Ha H AD y Hy.
   assert (Hy' : In y (a::u)).
   { rewrite <- (Add_in AD). apply H; simpl; auto. }
   destruct Hy'; [ subst; now elim Ha | trivial ].
  Qed.

End Add.

(********************************)
(** ** Lists without redundancy *)
(********************************)

Section ReDun.

  Variable A : Type.
  Variable HA : CompDec A.
  (** Not handled by sniper: inductive predicate **)

  Inductive NoDup : list A -> Prop :=
    | NoDup_nil : NoDup nil
    | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).

  Lemma NoDup_Add a l l' : Add a l l' -> (NoDup l' <-> NoDup l /\ ~In a l).
  Proof. idtac "NoDup_Add".
   induction 1 as [l|x l l' AD IH].
   - split; [ inversion_clear 1; now split | now constructor ].
   - split.
     + inversion_clear 1. rewrite IH in *. rewrite (Add_in AD) in *.
       simpl in *; split; try constructor; intuition.
     + intros (N,IN). inversion_clear N. constructor.
       * rewrite (Add_in AD); simpl in *; intuition.
       * apply IH. split; trivial. simpl in *; intuition.
  Qed.

  Lemma NoDup_remove l l' a :
    NoDup (l++a::l') -> NoDup (l++l') /\ ~In a (l++l').
  Proof. idtac "NoDup_remove".
  apply NoDup_Add. apply Add_app.
  Qed.

  Lemma NoDup_remove_1 l l' a : NoDup (l++a::l') -> NoDup (l++l').
  Proof. idtac "NoDup_remove_1".
  intros. now apply NoDup_remove with a.
  Qed.

  Lemma NoDup_remove_2 l l' a : NoDup (l++a::l') -> ~In a (l++l').
  Proof. idtac "NoDup_remove_2".
  intros. now apply NoDup_remove.
  Qed.

  Theorem NoDup_cons_iff a l:
    NoDup (a::l) <-> ~ In a l /\ NoDup l.
  Proof. idtac "NoDup_cons_iff".
    split.
    + inversion_clear 1. now split.
    + now constructor.
  Qed.

  Lemma NoDup_rev l : NoDup l -> NoDup (rev l).
  Proof. idtac "NoDup_rev".
  induction l as [|a l IHl]; simpl; intros Hnd; [ constructor | ].
    inversion_clear Hnd as [ | ? ? Hnin Hndl ].
    assert (Add a (rev l) (rev l ++ a :: nil)) as Hadd
      by (rewrite <- (app_nil_r HA (rev l)) at 1; apply Add_app).
    apply NoDup_Add in Hadd; apply Hadd; intuition.
    now apply Hnin, in_rev.
  Qed.

  Lemma NoDup_filter f l : NoDup l -> NoDup (filter f l).
  Proof. idtac "NoDup_filter".
   induction l as [|a l IHl]; simpl; intros Hnd; auto.
    apply NoDup_cons_iff in Hnd.
    destruct (f a); [ | intuition ].
    apply NoDup_cons_iff; split; [intro H|]; intuition.
    apply filter_In in H; intuition.
  Qed.

  (** Effective computation of a list without duplicates *)

  Hypothesis decA: forall x y : A, {x = y} + {x <> y}.

  Fixpoint nodup (l : list A) : list A :=
    match l with
      | [] => []
      | x::xs => if in_dec decA x xs then nodup xs else x::(nodup xs)
    end.

  Lemma nodup_fixed_point (l : list A) :
    NoDup l -> nodup l = l.
  Proof. idtac "nodup_fixed_point".
   induction l as [| x l IHl]; [auto|]. intros H.
    simpl. destruct (in_dec decA x l) as [Hx | Hx]; rewrite NoDup_cons_iff in H.
    - destruct H as [H' _]. contradiction.
    - destruct H as [_ H']. apply IHl in H'. rewrite -> H'. reflexivity.
  Qed.

  Lemma nodup_In l x : In x (nodup l) <-> In x l.
  Proof. idtac "nodup_In".
   induction l as [|a l' Hrec]; simpl.
    - reflexivity.
    - destruct (in_dec decA a l'); simpl; rewrite Hrec.
      * now intuition subst.
      * reflexivity.
  Qed.

  Lemma nodup_incl l1 l2 : incl l1 (nodup l2) <-> incl l1 l2.
  Proof. idtac "nodup_incl".
  split; intros Hincl a Ha; apply nodup_In; intuition.
  Qed.

  Lemma NoDup_nodup l: NoDup (nodup l).
  Proof. idtac "NoDup_nodup".
  induction l as [|a l' Hrec]; simpl.
    - constructor.
    - destruct (in_dec decA a l'); simpl.
      * assumption.
      * constructor; [ now rewrite nodup_In | assumption].
  Qed.

  Lemma nodup_inv k l a : nodup k = a :: l -> ~ In a l.
  Proof. idtac "nodup_inv".
   intros H.
    assert (H' : NoDup (a::l)).
    { rewrite <- H. apply NoDup_nodup. }
    now inversion_clear H'.
  Qed.

  Theorem NoDup_count_occ l:
    NoDup l <-> (forall x:A, count_occ decA l x <= 1).
  Proof. idtac "NoDup_count_occ".
  induction l as [| a l' Hrec].
    - simpl; split; auto. constructor.
    - rewrite NoDup_cons_iff, Hrec, (count_occ_not_In decA). clear Hrec. split.
      + intros (Ha, H) x. simpl. destruct (decA a x); auto.
        subst; now rewrite Ha.
      + intro H; split.
        * specialize (H a). rewrite count_occ_cons_eq in H; trivial.
          now inversion H.
        * intros x. specialize (H x). simpl in *. destruct (decA a x); auto.
          now apply Nat.lt_le_incl.
  Qed.

  Theorem NoDup_count_occ' l:
    NoDup l <-> (forall x:A, In x l -> count_occ decA l x = 1).
  Proof. idtac "NoDup_count_occ'".
  rewrite NoDup_count_occ.
    setoid_rewrite (count_occ_In decA). unfold gt, lt in *.
    split; intros H x; specialize (H x);
    set (n := count_occ decA l x) in *; clearbody n.
    (* the rest would be solved by omega if we had it here... *)
    - now apply Nat.le_antisymm.
    - destruct (Nat.le_gt_cases 1 n); trivial.
      + rewrite H; trivial.
      + now apply Nat.lt_le_incl.
  Qed.

  (** Alternative characterisations of being without duplicates,
      thanks to [nth_error] and [nth] *)

  Lemma NoDup_nth_error l :
    NoDup l <->
    (forall i j, i<length l -> nth_error l i = nth_error l j -> i = j).
  Proof. idtac "NoDup_nth_error".
    split.
    { intros H; induction H as [|a l Hal Hl IH]; intros i j Hi E.
      - inversion Hi.
      - destruct i, j; simpl in *; auto.
        * elim Hal. eapply nth_error_In; eauto.
        * elim Hal. eapply nth_error_In; eauto.
        * f_equal. now apply IH;[apply Nat.succ_lt_mono|]. }
    { induction l as [|a l IHl]; intros H; constructor.
      * intro Ha. apply In_nth_error in Ha. destruct Ha as (n,Hn).
        assert (n < length l) by (now rewrite <- List.nth_error_Some).
        rewrite <- List.nth_error_Some in H0.
        specialize (H 0 (S n)). simpl in H. now discriminate H; [apply Nat.lt_0_succ|].
      * apply IHl.
        intros i j Hi %Nat.succ_lt_mono E. now apply eq_add_S, H. }
  Qed.

  Lemma NoDup_nth l d :
    NoDup l <->
    (forall i j, i<length l -> j<length l ->
       nth i l d = nth j l d -> i = j).
  Proof. idtac "NoDup_nth".
    rewrite NoDup_nth_error. split.
    - intros H i j ? ? E. apply H; [assumption|].
      now rewrite !(nth_error_nth' l d), E.
    - intros H i j ? E. assert (j < length l).
      { apply nth_error_Some. rewrite <- E. now apply nth_error_Some. }
      apply H; [assumption ..|].
      rewrite !(nth_error_nth' l d) in E; congruence.
  Qed.

  (** Having [NoDup] hypotheses bring more precise facts about [incl]. *)

  Lemma NoDup_incl_length l l' :
    NoDup l -> incl l l' -> length l <= length l'.
  Proof. idtac "NoDup_incl_length".
 intros N. revert l'. induction N as [|a l Hal N IH]; simpl.
   - intros. now apply Nat.le_0_l.
   - intros l' H.
     destruct (Add_inv a l') as (l'', AD). { apply H; simpl; auto. }
     rewrite (Add_length AD). apply le_n_S. apply IH.
     now apply incl_Add_inv with a l'.
  Qed.

  Lemma NoDup_length_incl l l' :
    NoDup l -> length l' <= length l -> incl l l' -> incl l' l.
  Proof. idtac "NoDup_length_incl".
  intros N. revert l'. induction N as [|a l Hal N IH].
   - intro l'; destruct l'; easy.
   - intros l' E H x Hx.
     destruct (Add_inv a l') as (l'', AD). { apply H; simpl; auto. }
     rewrite (Add_in AD) in Hx. simpl in Hx.
     destruct Hx as [Hx|Hx]; [left; trivial|right].
     revert x Hx. apply (IH l''); trivial.
     * apply Nat.succ_le_mono. now rewrite <- (Add_length AD).
     * now apply incl_Add_inv with a l'.
  Qed.

  Lemma NoDup_incl_NoDup (l l' : list A) : NoDup l ->
    length l' <= length l -> incl l l' -> NoDup l'.
  Proof. idtac "NoDup_incl_NoDup".
   revert l'; induction l as [|a l IHl]; simpl; intros l' Hnd Hlen Hincl.
    - now destruct l'; inversion Hlen.
    - assert (In a l') as Ha by now apply Hincl; left.
      apply in_split in Ha as [l1' [l2' ->]].
      inversion_clear Hnd as [|? ? Hnin Hnd'].
      apply (NoDup_Add (Add_app a l1' l2')); split.
      + apply IHl; auto.
        * rewrite List.app_length.
          rewrite List.app_length in Hlen; simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
          now apply Nat.succ_le_mono.
        * apply (incl_Add_inv (u:= l1' ++ l2')) in Hincl; auto.
          apply Add_app.
      + intros Hnin'.
        assert (incl (a :: l) (l1' ++ l2')) as Hincl''.
        { apply List.incl_tran with (l1' ++ a :: l2'); auto.
          intros x Hin.
          apply List.in_app_or in Hin as [Hin|[->|Hin]]; intuition. }
        apply NoDup_incl_length in Hincl''; [ | now constructor ].
        apply (Nat.nle_succ_diag_l (length l1' + length l2')).
        rewrite_all List.app_length.
        simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
        now transitivity (S (length l)). 
  Qed.

End ReDun.

(** NoDup and map *)

(** NB: the reciprocal result holds only for injective functions,
    see FinFun.v *)

Lemma NoDup_map_inv A B (f:A->B) l : NoDup (map f l) -> NoDup l.
Proof. idtac "NoDup_map_inv".
 induction l; simpl; inversion_clear 1; subst; constructor; auto.
 intro H; now apply (List.in_map f) in H.
Qed.

(***********************************)
(** ** Sequence of natural numbers *)
(***********************************)

Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

  Fixpoint seq (start len:nat) : list nat :=
    match len with
      | 0 => nil
      | S len => start :: seq (S start) len
    end.

  Lemma cons_seq : forall len start, start :: seq (S start) len = seq start (S len).
  Proof. idtac "cons_seq".
    reflexivity.
  Qed.

  Lemma seq_length : forall len start, length (seq start len) = len.
  Proof. idtac "seq_length".
    Time intro len; induction len; snipe.
  Qed.

  Lemma seq_nth : forall len start n d,
    n < len -> nth n (seq start len) d = start+n.
  Proof. idtac "seq_nth".
    intro len; induction len as [|len IHlen]; intros start n d H.
    inversion H.
    simpl seq.
    destruct n; simpl. now rewrite Nat.add_0_r.
    now rewrite IHlen; [rewrite Nat.add_succ_r|apply Nat.succ_lt_mono].
  Qed.

  Lemma seq_shift : forall len start,
    map S (seq start len) = seq (S start) len.
  Proof. idtac "seq_shift".
    intro len; induction len as [|len IHlen]; simpl; auto.
    intros.
    now rewrite IHlen.
  Qed.

  Lemma in_seq len start n :
    In n (seq start len) <-> start <= n < start+len.
  Proof. idtac "in_seq".
   revert start. induction len as [|len IHlen]; simpl; intros start.
    { rewrite Nat.add_0_r. split;[easy|].
      intros (H,H'). apply (Nat.lt_irrefl start).
      eapply Nat.le_lt_trans; eassumption. }
    - rewrite IHlen, Nat.add_succ_r; simpl; split.
      + intros H. destruct H. subst; intuition. assert (H1 : start <= S start). auto.
split.
    apply Coq.Arith.Le.le_Sn_le. destruct H. assumption. destruct H. assumption.
      + intros (H,H'). inversion H.
        * now left.
        * right. subst. now split; [apply -> Nat.succ_le_mono|].
  Qed.

  Lemma seq_NoDup len start : NoDup (seq start len).
  Proof. idtac "seq_NoDup".
   revert start; induction len as [|len IH];
     intros start; simpl; constructor; trivial.
   rewrite in_seq. intros (H,_). now apply (Nat.lt_irrefl start).
  Qed.

  Lemma seq_app : forall len1 len2 start,
    seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
  Proof. idtac "seq_app".
    Time intro len1; induction len1 as [|len1' IHlen]; snipe. 
  Qed.

  Lemma seq_S : forall len start, seq start (S len) = seq start len ++ [start + len].
  Proof. idtac "seq_S".
  intros len start.
   change [start + len] with (seq (start + len) 1).
   rewrite <- seq_app.
   rewrite Nat.add_succ_r, Nat.add_0_r; reflexivity.
  Qed.

End NatSeq.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Prop.

    Inductive Exists : list A -> Prop :=
      | Exists_cons_hd : forall x l, P x -> Exists (x::l)
      | Exists_cons_tl : forall x l, Exists l -> Exists (x::l).

    #[local]
    Hint Constructors Exists : core.

    Lemma Exists_exists (l:list A) :
      Exists l <-> (exists x, In x l /\ P x).
    Proof. idtac "Exists_exists".
      split.
      - induction 1; firstorder.
      - induction l; firstorder (subst; auto).
    Qed.

    Lemma Exists_nth l :
      Exists l <-> exists i d, i < length l /\ P (nth i l d).
    Proof. idtac "Exists_nth".
    split.
      - intros HE; apply Exists_exists in HE.
        destruct HE as [a [Hin HP]].
        apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
        rewrite <- Heq in HP.
        now exists i; exists a.
      - intros [i [d [Hl HP]]].
        apply Exists_exists; exists (nth i l d); split.
        apply List.nth_In; assumption.
        assumption.
    Qed.

    Lemma Exists_nil : Exists nil <-> False.
    Proof. idtac "Exists_nil". split; inversion 1. Qed.

    Lemma Exists_cons x l:
      Exists (x::l) <-> P x \/ Exists l.
    Proof. idtac "Exists_cons". split; inversion 1; auto. Qed.

    Lemma Exists_app l1 l2 :
      Exists (l1 ++ l2) <-> Exists l1 \/ Exists l2.
    Proof. idtac "Exists_app".
      induction l1; simpl; split; intros HE; try now intuition.
      - inversion_clear HE; intuition.
      - destruct HE as [HE|HE]; intuition.
        inversion_clear HE; intuition.
    Qed.

    Lemma Exists_rev l : Exists l -> Exists (rev l).
    Proof. idtac "Exists_rev".
      induction l; intros HE; intuition.
      inversion_clear HE; simpl; apply Exists_app; intuition.
    Qed.

    Lemma Exists_dec l:
      (forall x:A, {P x} + { ~ P x }) ->
      {Exists l} + {~ Exists l}.
    Proof. idtac "Exists_dec".
      intro Pdec. induction l as [|a l' Hrec].
      - right. abstract now rewrite Exists_nil.
      - destruct Hrec as [Hl'|Hl'].
        + left. now apply Exists_cons_tl.
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Exists_cons_hd.
          * right. abstract now inversion 1.
   Qed.

    Lemma Exists_fold_right l :
      Exists l <-> fold_right (fun x => or (P x)) False l.
    Proof. idtac "Exists_fold_right".
      induction l; simpl; split; intros HE; try now inversion HE; intuition.
    Qed.

    Lemma incl_Exists l1 l2 : incl l1 l2 -> Exists l1 -> Exists l2.
    Proof. idtac "incl_Exists".
      intros Hincl HE.
      apply Exists_exists in HE; destruct HE as [a [Hin HP]].
      apply Exists_exists; exists a; intuition.
    Qed.

    Inductive Forall : list A -> Prop :=
      | Forall_nil : Forall nil
      | Forall_cons : forall x l, P x -> Forall l -> Forall (x::l).

    #[local]
    Hint Constructors Forall : core.

    Lemma Forall_inv : forall (a:A) l, Forall (a :: l) -> P a.
    Proof. idtac "Forall_inv".
      intros a l H; inversion H; trivial.
    Qed.

    Theorem Forall_inv_tail : forall (a:A) l, Forall (a :: l) -> Forall l.
    Proof. idtac "Forall_inv_tail".
      intros a l H; inversion H; trivial.
    Qed.

    Lemma Forall_nil_iff : Forall [] <-> True.
    Proof. idtac "Forall_nil_iff".
      easy.
    Qed.

    Lemma Forall_cons_iff : forall (a:A) l, Forall (a :: l) <-> P a /\ Forall l.
    Proof. idtac "Forall_cons_iff".
      intros. now split; [intro H; inversion H|constructor].
   Qed.

    Lemma Forall_forall (l:list A):
      Forall l <-> (forall x, List.In x l -> P x).
    Proof. idtac "Forall_forall".
      split.
      - induction 1; firstorder (subst; auto).
      - induction l.
        + intros ; apply Forall_nil_iff. exact I.
        + intros H. apply Forall_cons. apply H. apply List.in_eq. 
apply IHl. intros x H1. apply H. apply in_cons. assumption. 
    Qed.

    Lemma Forall_nth l :
      Forall l <-> forall i d, i < length l -> P (nth i l d).
    Proof. idtac "Forall_nth".
   split.
      - intros HF i d Hl.
        apply (Forall_forall l).
        assumption.
        apply List.nth_In; assumption.
      - intros HF.
        apply Forall_forall; intros a Hin.
        apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
        rewrite <- Heq; intuition.
    Qed.

    Lemma Forall_app l1 l2 :
      Forall (l1 ++ l2) <-> Forall l1 /\ Forall l2.
    Proof. idtac "Forall_app".
      induction l1 as [|a l1 IH]; cbn.
      - now rewrite Forall_nil_iff.
      - now rewrite !Forall_cons_iff, IH, and_assoc.
    Qed.

    Lemma Forall_elt a l1 l2 : Forall (l1 ++ a :: l2) -> P a.
    Proof. idtac "Forall_elt".
      intros HF; apply Forall_app in HF; destruct HF as [HF1 HF2]; now inversion HF2.
    Qed.

    Lemma Forall_rev l : Forall l -> Forall (rev l).
    Proof. idtac "Forall_rev".
      induction l; intros HF; [assumption|].
      inversion_clear HF; simpl; apply Forall_app; intuition.
    Qed.

    Lemma Forall_rect : forall (Q : list A -> Type),
      Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, Forall l -> Q l.
    Proof. idtac "Forall_rect".
      intros Q H H' l; induction l; intro; [|eapply H', Forall_inv]; eassumption.
    Qed.

    Lemma Forall_dec :
      (forall x:A, {P x} + { ~ P x }) ->
      forall l:list A, {Forall l} + {~ Forall l}.
    Proof. idtac "Forall_dec".
      intros Pdec l. induction l as [|a l' Hrec].
      - left. apply Forall_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Qed.

    Lemma Forall_fold_right l :
      Forall l <-> fold_right (fun x => and (P x)) True l.
    Proof. idtac "Forall_fold_right".
      induction l; simpl; split; intros HF; try now inversion HF; intuition.
    Qed.

    Lemma incl_Forall l1 l2 : incl l2 l1 -> Forall l1 -> Forall l2.
    Proof. idtac "incl_Forall".
      intros Hincl HF.
      apply Forall_forall; intros a Ha.
      apply (Forall_forall l1); intuition.
    Qed.

  End One_predicate.

  Lemma map_ext_Forall B : forall (f g : A -> B) l,
    Forall (fun x => f x = g x) l -> map f l = map g l.
  Proof. idtac "map_ext_Forall".
    intros; apply map_ext_in, Forall_forall; assumption.
  Qed.

  Theorem Exists_impl : forall (P Q : A -> Prop), (forall a : A, P a -> Q a) ->
    forall l, Exists P l -> Exists Q l.
  Proof. idtac "Exists_impl".
    intros P Q H l H0.
    induction H0 as [x l H0|x l H0 IHExists].
    apply (Exists_cons_hd Q x l (H x H0)).
    apply (Exists_cons_tl x IHExists).
  Qed.

  Lemma Exists_or : forall (P Q : A -> Prop) l,
    Exists P l \/ Exists Q l -> Exists (fun x => P x \/ Q x) l.
  Proof. idtac "Exists_or".
    intros P Q l; induction l as [|a l IHl]; intros [H | H]; inversion H; subst.
    1,3: apply Exists_cons_hd; auto.
    all: apply Exists_cons_tl, IHl; auto.
  Qed.

  Lemma Exists_or_inv : forall (P Q : A -> Prop) l,
    Exists (fun x => P x \/ Q x) l -> Exists P l \/ Exists Q l.
  Proof. idtac "Exists_or_inv".
    intros P Q l; induction l as [|a l IHl];
     intro Hl; inversion Hl as [ ? ? H | ? ? H ]; subst.
    - inversion H; now repeat constructor.
    - destruct (IHl H); now repeat constructor.
  Qed.

  Lemma Forall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
    forall l, Forall P l -> Forall Q l.
  Proof. idtac "Forall_impl".
    intros P Q H l. rewrite !Forall_forall. firstorder.
  Qed.

  Lemma Forall_and : forall (P Q : A -> Prop) l,
    Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
  Proof. idtac "Forall_and".
    intros P Q l; induction l; intros HP HQ; constructor; inversion HP; inversion HQ; auto.
  Qed.

  Lemma Forall_and_inv : forall (P Q : A -> Prop) l,
    Forall (fun x => P x /\ Q x) l -> Forall P l /\ Forall Q l.
  Proof. idtac "Forall_and_inv".
    intros P Q l; induction l; intro Hl; split; constructor; inversion Hl; firstorder.
  Qed.

  Lemma Forall_Exists_neg (P:A->Prop)(l:list A) :
    Forall (fun x => ~ P x) l <-> ~(Exists P l).
  Proof. idtac "Forall_Exists_neg".
    rewrite Forall_forall, Exists_exists. firstorder.
  Qed.

  Lemma Exists_Forall_neg (P:A->Prop)(l:list A) :
    (forall x, P x \/ ~P x) ->
    Exists (fun x => ~ P x) l <-> ~(Forall P l).
  Proof. idtac "Exists_Forall_neg".
    intro Dec.
    split.
    - rewrite Forall_forall, Exists_exists; firstorder.
    - intros NF.
      induction l as [|a l IH].
      + destruct NF. constructor.
      + destruct (Dec a) as [Ha|Ha].
        * apply Exists_cons_tl, IH. contradict NF. now constructor.
        * now apply Exists_cons_hd.
  Qed.

  Lemma neg_Forall_Exists_neg (P:A->Prop) (l:list A) :
    (forall x:A, {P x} + { ~ P x }) ->
    ~ Forall P l ->
    Exists (fun x => ~ P x) l.
  Proof. idtac "neg_Forall_Exists_neg".
    intro Dec.
    apply Exists_Forall_neg; intros x.
    destruct (Dec x); auto.
  Qed.

  Lemma Forall_Exists_dec (P:A->Prop) :
    (forall x:A, {P x} + { ~ P x }) ->
    forall l:list A,
    {Forall P l} + {Exists (fun x => ~ P x) l}.
  Proof. idtac "Forall_Exists_dec".
    intros Pdec l.
    destruct (Forall_dec P Pdec l); [left|right]; trivial.
    now apply neg_Forall_Exists_neg.
  Defined.

  Lemma incl_Forall_in_iff l l' :
    incl l l' <-> Forall (fun x => In x l') l.
  Proof. idtac "incl_Forall_in_iff". now rewrite Forall_forall; split. Qed.

End Exists_Forall.

#[global]
Hint Constructors Exists : core.
#[global]
Hint Constructors Forall : core.

Lemma Exists_map A B (f : A -> B) P l :
  Exists P (map f l) <-> Exists (fun x => P (f x)) l.
Proof. idtac "Exists_map".
  induction l as [|a l IHl].
  - cbn. now rewrite Exists_nil.
  - cbn. now rewrite ?Exists_cons, IHl.
Qed.

Lemma Exists_concat A P (ls : list (list A)) :
  Exists P (concat ls) <-> Exists (Exists P) ls.
Proof. idtac "Exists_concat".
  induction ls as [|l ls IHls].
  - cbn. now rewrite Exists_nil.
  - cbn. now rewrite Exists_app, Exists_cons, IHls.
Qed.

Lemma Exists_flat_map A B P ls (f : A -> list B) :
  Exists P (flat_map f ls) <-> Exists (fun d => Exists P (f d)) ls.
Proof. idtac "Exists_flat_map".
  now rewrite flat_map_concat_map, Exists_concat, Exists_map.
Qed.

Lemma Forall_map A B (f : A -> B) P l :
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof. idtac "Forall_map".
  induction l as [|a l IHl]; cbn.
  - now rewrite !Forall_nil_iff.
  - now rewrite !Forall_cons_iff, IHl.
Qed.

Lemma Forall_concat A P (ls : list (list A)) :
  Forall P (concat ls) <-> Forall (Forall P) ls.
Proof. idtac "Forall_concat".
  induction ls as [|l ls IHls]; cbn.
  - now rewrite !Forall_nil_iff.
  - now rewrite Forall_app, Forall_cons_iff, IHls.
Qed.

Lemma Forall_flat_map A B P ls (f : A -> list B) :
  Forall P (flat_map f ls) <-> Forall (fun d => Forall P (f d)) ls.
Proof. idtac "Forall_flat_map".
  now rewrite flat_map_concat_map, Forall_concat, Forall_map.
Qed.

Lemma exists_Forall A B : forall (P : A -> B -> Prop) l,
  (exists k, Forall (P k) l) -> Forall (fun x => exists k, P k x) l.
Proof. idtac "exists_Forall".
  intros P l; induction l as [|a l IHl]; intros [k HF]; constructor; inversion_clear HF.
  - now exists k.
  - now apply IHl; exists k.
Qed.

Lemma Forall_image A B : forall (f : A -> B) l,
  Forall (fun y => exists x, y = f x) l <-> exists l', l = map f l'.
Proof. idtac "Forall_image".
  intros f l; induction l as [|a l IHl]; split; intros HF.
  - exists nil; reflexivity.
  - constructor.
  - apply Forall_cons_iff in HF as [[x ->] [l' ->] %IHl].
    now exists (x :: l').
  - destruct HF as [l' Heq].
    symmetry in Heq; apply map_eq_cons in Heq.
    destruct Heq as (x & tl & ? & ? & ?); subst.
    constructor.
    + now exists x.
    + now apply IHl; exists tl.
Qed.

Lemma concat_nil_Forall A : forall (l : list (list A)),
  concat l = nil <-> Forall (fun x => x = nil) l.
Proof. idtac "concat_nil_Forall".
  intro l; induction l as [|a l IHl]; simpl; split; intros Hc; auto.
  - apply List.app_eq_nil in Hc.
    constructor; firstorder.
  - inversion Hc; subst; simpl.
    now apply IHl.
Qed.

Lemma in_flat_map_Exists A B : forall (f : A -> list B) x l,
  In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
Proof. idtac "in_flat_map_Exists".
  intros f x l; rewrite in_flat_map.
  split; apply Exists_exists.
Qed.

Lemma notin_flat_map_Forall A B : forall (f : A -> list B) x l,
  ~ In x (flat_map f l) <-> Forall (fun y => ~ In x (f y)) l.
Proof. idtac "notin_flat_map_Forall".
  intros f x l; rewrite Forall_Exists_neg.
  apply not_iff_compat, in_flat_map_Exists.
Qed.


Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Prop.

  Inductive Forall2 : list A -> list B -> Prop :=
    | Forall2_nil : Forall2 [] []
    | Forall2_cons : forall x y l l',
      R x y -> Forall2 l l' -> Forall2 (x::l) (y::l').

  #[local]
  Hint Constructors Forall2 : core.

  Theorem Forall2_refl : Forall2 [] [].
  Proof. idtac "Forall2_refl". intros; apply Forall2_nil. Qed.

  Theorem Forall2_app_inv_l : forall l1 l2 l',
    Forall2 (l1 ++ l2) l' ->
    exists l1' l2', Forall2 l1 l1' /\ Forall2 l2 l2' /\ l' = l1' ++ l2'.
  Proof. idtac "Forall2_app_inv_l".
    intro l1; induction l1 as [|a l1 IHl1]; intros l2 l' H.
      exists [], l'; auto.
      simpl in H; inversion H as [|? y ? ? ? H4]; subst; clear H.
      apply IHl1 in H4 as (l1' & l2' & Hl1 & Hl2 & ->).
      exists (y::l1'), l2'; simpl; auto.
  Qed.

  Theorem Forall2_app_inv_r : forall l1' l2' l,
    Forall2 l (l1' ++ l2') ->
    exists l1 l2, Forall2 l1 l1' /\ Forall2 l2 l2' /\ l = l1 ++ l2.
  Proof. idtac "Forall2_app_inv_r".
    intro l1'; induction l1' as [|a l1' IHl1']; intros l2' l H.
      exists [], l; auto.
      simpl in H; inversion H as [|x ? ? ? ? H4]; subst; clear H.
      apply IHl1' in H4 as (l1 & l2 & Hl1 & Hl2 & ->).
      exists (x::l1), l2; simpl; auto.
  Qed.

  Theorem Forall2_app : forall l1 l2 l1' l2',
    Forall2 l1 l1' -> Forall2 l2 l2' -> Forall2 (l1 ++ l2) (l1' ++ l2').
  Proof. idtac "Forall2_app".
    intros l1 l2 l1' l2' H H0. induction l1 in l1', H, H0 |- *; inversion H; subst; simpl; auto.
  Qed.
End Forall2.

#[global]
Hint Constructors Forall2 : core.

Section ForallPairs.

  (** [ForallPairs] : specifies that a certain relation should
    always hold when inspecting all possible pairs of elements of a list. *)

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Definition ForallPairs l :=
    forall a b, In a l -> In b l -> R a b.

  (** [ForallOrdPairs] : we still check a relation over all pairs
     of elements of a list, but now the order of elements matters. *)

  Inductive ForallOrdPairs : list A -> Prop :=
    | FOP_nil : ForallOrdPairs nil
    | FOP_cons : forall a l,
      Forall (R a) l -> ForallOrdPairs l -> ForallOrdPairs (a::l).

  #[local]
  Hint Constructors ForallOrdPairs : core.

  Lemma ForallOrdPairs_In : forall l,
    ForallOrdPairs l ->
    forall x y, In x l -> In y l -> x=y \/ R x y \/ R y x.
  Proof. idtac "ForallOrdPairs_In".
    induction 1.
    inversion 1.
    simpl; destruct 1; destruct 1; subst; auto.
    right; left. apply -> Forall_forall; eauto.
    right; right. apply -> Forall_forall; eauto.
  Qed.

  (** [ForallPairs] implies [ForallOrdPairs]. The reverse implication is true
    only when [R] is symmetric and reflexive. *)

  Lemma ForallPairs_ForallOrdPairs l: ForallPairs l -> ForallOrdPairs l.
  Proof. idtac "ForallPairs_ForallOrdPairs".
    induction l as [|a l IHl]; [easy|].
    intros H. constructor.
    - rewrite Forall_forall. intros; apply H; simpl; auto.
    - apply IHl. red; intros; apply H; simpl; auto.
  Qed.

  Lemma ForallOrdPairs_ForallPairs :
    (forall x, R x x) ->
    (forall x y, R x y -> R y x) ->
    forall l, ForallOrdPairs l -> ForallPairs l.
  Proof. idtac "ForallOrdPairs_ForallPairs".
    intros Refl Sym l Hl x y Hx Hy.
    destruct (ForallOrdPairs_In Hl _ _ Hx Hy); subst; intuition.
  Qed.
End ForallPairs.

Section Repeat.

  Variable A : Type.
  Variable (HA : CompDec A).
  Fixpoint repeat (x : A) (n: nat ) :=
    match n with
      | O => []
      | S k => x::(repeat x k)
    end.

  Theorem repeat_length x n:
    length (repeat x n) = n.
  Proof. idtac "repeat_length".
    Time induction n as [| k Hrec]; snipe.
  Qed.

  Theorem repeat_spec n x y:
    Inb y (repeat x n) -> y=x.
  Proof. idtac "repeat_spec".
    Time induction n ; snipe.
  Qed.

  Lemma repeat_cons n a :
    a :: repeat a n = repeat a n ++ (a :: nil).
  Proof. idtac "repeat_cons".
    Time induction n ; snipe.
  Qed.

  Lemma repeat_app x n m :
    repeat x (n + m) = repeat x n ++ repeat x m.
  Proof. idtac "repeat_app".
    Time induction n; snipe.
  Qed.

  Lemma repeat_eq_app x n l1 l2 :
    repeat x n = l1 ++ l2 -> repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
  Proof. idtac "repeat_eq_app".
    revert n; induction l1 as [|a l1 IHl1]; simpl; intros n Hr; subst.
    - repeat split; now rewrite repeat_length.
    - destruct n; inversion Hr as [ [Heq Hr0] ]; subst.
      now apply IHl1 in Hr0 as [-> ->].
  Qed.

  Lemma repeat_eq_cons x y n l :
    repeat x n = y :: l -> x = y /\ repeat x (pred n) = l.
  Proof. idtac "repeat_eq_cons". 
      intros Hr.
    destruct n; inversion_clear Hr; auto.
  Qed.

  Lemma repeat_eq_elt x y n l1 l2 :
    repeat x n = l1 ++ y :: l2 -> x = y /\ repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
  Proof. idtac "repeat_eq_elt".
   intros Hr; apply repeat_eq_app in Hr as [Hr1 Hr2]; subst.
    apply repeat_eq_cons in Hr2; intuition.
  Qed.

  Lemma Forall_eq_repeat x l :
    Forall (eq x) l -> l = repeat x (length l).
  Proof. idtac "Forall_eq_repeat".
    induction l as [|a l IHl]; simpl; intros HF; auto.
    inversion_clear HF as [ | ? ? ? HF']; subst.
    now rewrite (IHl HF') at 1.
  Qed.

 Hypothesis decA : forall x y : A, {x = y}+{x <> y}.

  Lemma count_occ_repeat_eq x y n : x = y -> count_occ decA (repeat y n) x = n.
  Proof. idtac "count_occ_repeat_eq".
    intros ->.
    induction n; cbn; auto.
    destruct (decA y y); auto.
    exfalso; intuition.
  Qed.

  Lemma count_occ_repeat_neq x y n : x <> y -> count_occ decA (repeat y n) x = 0.
  Proof. idtac "count_occ_repeat_neq".
    intros Hneq.
    induction n; cbn; auto.
    destruct (decA y x); auto.
    exfalso; intuition.
  Qed.

  Lemma count_occ_unique x l : count_occ decA l x = length l -> l = repeat x (length l).
  Proof. idtac "count_occ_unique".
    induction l as [|h l]; cbn; intros Hocc; auto.
    destruct (decA h x).
    - f_equal; intuition.
    - assert (Hb := count_occ_bound decA x l).
      rewrite Hocc in Hb.
      exfalso; apply (Nat.nle_succ_diag_l _ Hb).
  Qed.

  Lemma count_occ_repeat_excl x l :
    (forall y, y <> x -> count_occ decA l y = 0) -> l = repeat x (length l).
  Proof. idtac "count_occ_repeat_excl".
    intros Hocc.
    apply Forall_eq_repeat, Forall_forall; intros z Hin.
    destruct (decA z x) as [Heq|Hneq]; auto.
    apply Hocc, count_occ_not_In in Hneq; intuition.
  Qed.

  Lemma count_occ_sgt l x : l = x :: nil <->
    count_occ decA l x = 1 /\ forall y, y <> x -> count_occ decA l y = 0.
  Proof. idtac "count_occ_sgt".
    split.
    - intros ->; cbn; split; intros; destruct decA; subst; intuition.
    - intros [Heq Hneq].
      apply count_occ_repeat_excl in Hneq.
      rewrite Hneq, count_occ_repeat_eq in Heq; trivial.
      now rewrite Heq in Hneq.
  Qed.

  Lemma nth_repeat a m n :
    nth n (repeat a m) a = a.
  Proof. idtac "nth_repeat".
    revert n. induction m as [|m IHm].
    - now intros [|n].
    - intros [|n]; [reflexivity|exact (IHm n)].
  Qed.

  Lemma nth_error_repeat a m n :
    n < m -> nth_error (repeat a m) n = Some a.
  Proof. idtac "nth_error_repeat".
    intro Hnm. rewrite (nth_error_nth' _ a).
    - now rewrite nth_repeat.
    - now rewrite repeat_length.
  Qed.

End Repeat.


Lemma repeat_to_concat A n (a:A) : CompDec A ->
  @repeat A a n = concat (repeat [a] n).
Proof. idtac "repeat_to_concat".
  Time induction n ; snipe. 
Qed.


(** Sum of elements of a list of [nat]: [list_sum] *)

Definition list_sum l := fold_right plus 0 l.

Lemma list_sum_app : forall l1 l2,
   list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof. idtac "list_sum_app".
intro l1; induction l1 as [|a l1 IHl1]; intros l2; [ reflexivity | ].
simpl; rewrite IHl1.
apply Nat.add_assoc.
Qed.

(** Max of elements of a list of [nat]: [list_max] *)

Definition list_max l := fold_right max 0 l.

Lemma list_max_app : forall l1 l2,
   list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
Proof. idtac "list_max_app".
intro l1; induction l1 as [|a l1 IHl1]; intros l2; [ reflexivity | ].
now simpl; rewrite IHl1, Nat.max_assoc.
Qed.

Lemma list_max_le : forall l n,
  list_max l <= n <-> Forall (fun k => k <= n) l.
Proof. idtac "list_max_le".
  intro l; induction l as [|a l IHl]; simpl; intros n; split.
  - now intros.
  - intros. now apply Nat.le_0_l.
  - intros [? ?] %Nat.max_lub_iff. now constructor; [|apply IHl].
  - now rewrite Forall_cons_iff, <- IHl, Nat.max_lub_iff.
Qed.

Lemma list_max_lt : forall l n, l <> nil ->
  list_max l < n <-> Forall (fun k => k < n) l.
Proof. idtac "list_max_lt".
intro l; induction l as [|a l IHl]; simpl; intros n Hnil; split; intros H; intuition.
- destruct l.
  + repeat constructor.
    now simpl in H; rewrite Nat.max_0_r in H.
  + apply Nat.max_lub_lt_iff in H.
    now constructor; [ | apply IHl ].
- destruct l; inversion_clear H as [ | ? ? Hlt HF ].
  + now simpl; rewrite Nat.max_0_r.
  + apply IHl in HF.
    * now apply Nat.max_lub_lt_iff.
    * intros Heq; inversion Heq.
Qed.

  
