From Hammer Require Import Hammer.

Hammer_version.
Hammer_objects.

Require Import PeanoNat.

#[universes(template)]
Inductive list' (A : Type) : Type :=
 | nil' : list' A
 | cons' : A -> list' A -> list' A.

Arguments nil' {A}.
Arguments cons' {A} a l.

Declare Scope list'_scope.
Delimit Scope list'_scope with list'.
Bind Scope list'_scope with list'.

Infix "::" := cons' (at level 60, right associativity) : list'_scope.

Register list' as core.list'.type.
Register nil' as core.list'.nil'.
Register cons' as core.list'.cons'.

Local Open Scope list'_scope.

Definition length {A : Type} : list' A -> nat :=
  fix length l :=
  match l with
   | nil' => O
   | _ :: l' => S (length l')
  end.

Definition app {A : Type} : list' A -> list' A -> list' A :=
  fix app l m :=
  match l with
   | nil' => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : list'_scope.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

(* To test the tactic, we need to redefine List as List', in order 
to forbid the use the lemma to be proven in the proof *)

#[local] Open Scope bool_scope.
Open Scope list'_scope.

(** Standard notations for lists'.
In a special module to avoid conflicts. *)
Module List'Notations.
Notation "[ ]" := nil' (format "[ ]") : list'_scope.
Notation "[ x ]" := (cons' x nil') : list'_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons' x (cons' y .. (cons' z nil) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : list'_scope.
End List'Notations.

Import List'Notations.

Section Lists'.

  Variable A : Type.

  (** Head and tail *)

  Definition hd (default:A) (l:list' A) :=
    match l with
      | [] => default
      | x :: _ => x
    end.

  Definition hd_error (l:list' A) :=
    match l with
      | [] => None
      | x :: _ => Some x
    end.

  Definition tl (l:list' A) :=
    match l with
      | [] => nil'
      | a :: m => m
    end.

  (** The [In] predicate *)
  Fixpoint In (a:A) (l:list' A) : Prop :=
    match l with
      | [] => False
      | b :: m => b = a \/ In a m
    end.

End Lists'.

Section Facts.

  Variable A : Type.

  (** *** Generic facts *)

  (** Discrimination *)
  Lemma nil_cons (x:A) (l:list' A) : [] <> x :: l.
  Proof. idtac "nil_cons".
   Time hammer.
  Qed.


  (** Destruction *)

  Lemma destruct_list (l : list' A) : {x:A & {tl:list' A | l = x::tl}}+{l = []}.
  Proof. idtac "destruct_list".
   Time hammer.
  Qed.

  Lemma hd_error_tl_repr l (a:A) r :
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. idtac "hd_error_tl_repr".
  Time hammer.
  Qed.

  Lemma hd_error_some_nil l (a:A) : hd_error l = Some a -> l <> nil'.
  Proof. idtac "hd_error_some_nil". Time hammer. Qed.

  Lemma length_zero_iff_nil (l : list' A):
    length l = 0 <-> l = [].
  Proof. idtac "length_zero_iff_nil".
   Time hammer.
  Qed.

  (** *** Head and tail *)

  Lemma hd_error_nil : hd_error (@nil' A) = None.
  Proof. idtac "hd_error_nil".
    Time hammer.
  Qed.

  Lemma hd_error_cons (l : list' A) (x : A) : hd_error (x::l) = Some x.
  Proof. idtac "hd_error_cons".
   Time hammer.
  Qed.


  (**************************)
  (** *** Facts about [app] *)
  (**************************)

  (** Discrimination *)
  Lemma app_cons_not_nil (x y:list' A) (a:A) : [] <> x ++ a :: y.
  Proof. idtac "app_cons_not_nil".
    Time hammer.
  Qed.


  (** Concat with [nil] *)
  Lemma app_nil_l (l:list' A) : [] ++ l = l.
  Proof. idtac "app_nil_l".
   Time hammer.
  Qed.

  Lemma app_nil_r (l:list' A) : l ++ [] = l.
  Proof. idtac "app_nil_r".
   Time induction l ; hammer.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Lemma app_nil_end (l:list' A) : l = l ++ [].
  Proof. idtac "app_nil_end". Time hammer. Qed.
  (* end hide *)

  (** [app] is associative *)
  Lemma app_assoc (l m n:list' A) : l ++ m ++ n = (l ++ m) ++ n.
  Proof. idtac "app_assoc".
    Time induction l; hammer.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Lemma app_assoc_reverse (l m n:list' A) : (l ++ m) ++ n = l ++ m ++ n.
  Proof. idtac "app_assoc_reverse". Time hammer. Qed.
  (* end hide *)

  (** [app] commutes with [cons] *)
  Lemma app_comm_cons (x y:list' A) (a:A) : a :: (x ++ y) = (a :: x) ++ y.
  Proof. idtac "app_comm_cons".
    Time hammer.
  Qed.

  (** Facts deduced from the result of a concatenation *)

  Lemma app_eq_nil (l l':list' A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof. idtac "app_eq_nil".
   now destruct l, l'.
  Qed.

  Lemma app_eq_unit (x y:list' A) (a:A) :
      x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof. idtac "app_eq_unit".
  Time hammer.
  Qed.

  Lemma elt_eq_unit l1 l2 (a b : A) :
    l1 ++ a :: l2 = [b] -> a = b /\ l1 = [] /\ l2 = [].
  Proof. idtac "elt_eq_unit".
    intros Heq.
    apply app_eq_unit in Heq.
    now destruct Heq as [[Heq1 Heq2]|[Heq1 Heq2]]; inversion_clear Heq2.
  Qed.

  Lemma app_eq_app X (x1 x2 y1 y2: list' X) : x1++x2 = y1++y2 ->
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
    forall (x y:list' A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof. idtac "app_inj_tail".
    intros x y a b [l [[-> Hl %eq_sym]|[-> Hl %eq_sym]]] %app_eq_app;
      apply elt_eq_unit in Hl as [? [-> ?]]; now rewrite app_nil_r.
  Qed.

  Lemma app_inj_tail_iff :
    forall (x y:list' A) (a b:A), x ++ [a] = y ++ [b] <-> x = y /\ a = b.
  Proof. idtac "app_inj_tail_iff".
   Time hammer.
  Qed.

  (** Compatibility with other operations *)

  Lemma app_length : forall l l' : list' A, length (l++l') = length l + length l'.
  Proof. idtac "app_length".
    Time intro l; induction l; hammer.
  Qed.

  Lemma last_length : forall (l : list' A) a, length (l ++ a :: nil') = S (length l).
  Proof. idtac "last_length".
    intros ; rewrite app_length ; simpl.
    rewrite Nat.add_succ_r, Nat.add_0_r; reflexivity.
  Qed.

  Lemma app_inv_head_iff:
   forall l l1 l2 : list' A, l ++ l1 = l ++ l2 <-> l1 = l2.
  Proof. idtac "app_inv_head_iff:
  ".
    Time intro l; induction l ; hammer.
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list' A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof. idtac "app_inv_head:
  ".
   Time hammer.
  Qed.

  Lemma app_inv_tail:
    forall l l1 l2 : list' A, l1 ++ l = l2 ++ l -> l1 = l2.
  Proof. idtac "app_inv_tail:
   ".
    intros l; induction l as [|a l IHl].
    - intros ? ?. now rewrite !app_nil_r.
    - intros ? ?. change (a :: l) with ([a] ++ l).
      rewrite !app_assoc. now intros [? ?] %IHl %app_inj_tail_iff.
  Qed.

  Lemma app_inv_tail_iff:
    forall l l1 l2 : list' A, l1 ++ l = l2 ++ l <-> l1 = l2.
  Proof. idtac "app_inv_tail_iff:
   ".
   Time hammer.
  Qed.

  (************************)
  (** *** Facts about [In] *)
  (************************)


  (** Characterization of [In] *)

  Lemma in_eq : forall (a:A) (l:list' A), In a (a :: l).
  Proof. idtac "in_eq".
  Time hammer.
  Qed.

  Lemma in_cons : forall (a b:A) (l:list' A), In b l -> In b (a :: l).
  Proof. idtac "in_cons".
    Time hammer.
  Qed.

  Lemma not_in_cons (x a : A) (l : list' A):
    ~ In x (a::l) <-> x<>a /\ ~ In x l.
  Proof. idtac "not_in_cons".
    Time hammer.
  Qed.

  Lemma in_nil : forall a:A, ~ In a [].
  Proof. idtac "in_nil".
  Time hammer.
  Qed.

  Lemma in_app_or : forall (l m:list' A) (a:A), In a (l ++ m) -> In a l \/ In a m.
  Proof. idtac "in_app_or".
    intros l m a. Time induction l; hammer.
  Qed.

  Lemma in_or_app : forall (l m:list' A) (a:A), In a l \/ In a m -> In a (l ++ m).
  Proof. idtac "in_or_app".
   Time intros l m a; induction l; hammer.
  Qed.

  Lemma in_app_iff : forall l l' (a:A), In a (l++l') <-> In a l \/ In a l'.
  Proof. idtac "in_app_iff".
    Time hammer.
  Qed.

  Lemma in_split : forall x (l:list' A), In x l -> exists l1 l2, l = l1++x::l2.
  Proof. idtac "in_split".
  intros x l; induction l as [|a l IHl]; simpl; [destruct 1|destruct 1 as [?|H]].
  subst a; auto.
  exists [], l; auto.
  destruct (IHl H) as (l1,(l2,H0)).
  exists (a::l1), l2; simpl. apply f_equal. auto.
  Qed.

  Lemma in_elt : forall (x:A) l1 l2, In x (l1 ++ x :: l2).
  Proof. idtac "in_elt".
  Time hammer.
  Qed.

  Lemma in_elt_inv : forall (x y : A) l1 l2,
    In x (l1 ++ y :: l2) -> x = y \/ In x (l1 ++ l2).
  Proof. idtac "in_elt_inv".
  Time hammer.
  Qed.

  (** Inversion *)
  Lemma in_inv : forall (a b:A) (l:list' A), In b (a :: l) -> a = b \/ In b l.
  Proof. idtac "in_inv". Time hammer. Qed.

  (** Decidability of [In] *)
  Lemma in_dec :
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (a:A) (l:list' A), {In a l} + {~ In a l}.
  Proof. idtac "in_dec".
    Time intros H a l; induction l as [| a0 l IHl] ; hammer.
  Defined.

End Facts.

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



(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:list' A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

  Fixpoint nth_ok (n:nat) (l:list' A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, other => false
      | S m, [] => false
      | S m, x :: t => nth_ok m t default
    end.

  Lemma nth_in_or_default :
    forall (n:nat) (l:list' A) (d:A), {In (nth n l d) l} + {nth n l d = d}.
  Proof. idtac "nth_in_or_default".
    Time intros n l d; revert n; induction l ; hammer.
  Qed.

  Lemma nth_S_cons :
    forall (n:nat) (l:list' A) (d a:A),
      In (nth n l d) l -> In (nth (S n) (a :: l) d) (a :: l).
  Proof. idtac "nth_S_cons".
    Time hammer.
  Qed.

  Fixpoint nth_error (l:list' A) (n:nat) {struct n} : option A :=
    match n, l with
      | O, x :: _ => Some x
      | S n, _ :: l => nth_error l n
      | _, _ => None
    end.

  Definition nth_default (default:A) (l:list' A) (n:nat) : A :=
    match nth_error l n with
      | Some x => x
      | None => default
    end.

  Lemma nth_default_eq :
    forall n l (d:A), nth_default d l n = nth n l d.
  Proof. idtac "nth_default_eq".
    Time intro n ; induction n ; hammer.
  Qed.

  (** Results about [nth] *)

  Lemma nth_In :
    forall (n:nat) (l:list' A) (d:A), n < length l -> In (nth n l d) l.
  Proof. idtac "nth_In".
  Time intro n ; induction n ; sauto.
  Qed.

  Lemma In_nth l x d : In x l ->
    exists n, n < length l /\ nth n l d = x.
  Proof. idtac "In_nth".
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto using Nat.lt_0_succ.
      * destruct (IH H) as (n & Hn & Hn').
        apply Nat.succ_lt_mono in Hn. now exists (S n).
  Qed.

  Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
  Proof. idtac "nth_overflow".
   Time intro l; induction l ; hammer.
  Qed.

  Lemma nth_indep :
    forall l n d d', n < length l -> nth n l d = nth n l d'.
  Proof. idtac "nth_indep".
    Time intro l; induction l as [|? ? IHl]; hammer.
  Qed.

  Lemma app_nth1 :
    forall l l' d n, n < length l -> nth n (l++l') d = nth n l d.
  Proof. idtac "app_nth1".
   Time intro l; induction l as [|? ? IHl]; hammer.
  Qed.

  Lemma app_nth2 :
    forall l l' d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
  Proof. idtac "app_nth2".
    Time intro l; induction l as [|? ? IHl]; hammer.
  Qed.

  Lemma app_nth2_plus : forall l l' d n,
    nth (length l + n) (l ++ l') d = nth n l' d.
  Proof. idtac "app_nth2_plus".
  Time hammer.
  Qed.

  Lemma nth_middle : forall l l' a d,
    nth (length l) (l ++ a :: l') d = a.
  Proof. idtac "nth_middle".
    intros.
    rewrite <- Nat.add_0_r at 1.
    apply app_nth2_plus.
  Qed.

  Lemma nth_split n l d : n < length l ->
    exists l1, exists l2, l = l1 ++ nth n l d :: l2 /\ length l1 = n.
  Proof. idtac "nth_split".
    revert l.
    induction n as [|n IH]; intros [|a l] H; try easy.
    - exists nil'; exists l; now simpl.
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

  Lemma nth_error_In l n x : nth_error l n = Some x -> In x l.
  Proof. idtac "nth_error_In".
    revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
    - injection 1; auto.
    - eauto.
  Qed.

  Lemma In_nth_error l x : In x l -> exists n, nth_error l n = Some x.
  Proof. idtac "In_nth_error".
    induction l as [|a l IH].
    - easy.
    - intros [H|[n ?] %IH].
      + subst; now exists 0.
      + now exists (S n).
  Qed.

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
    - exists nil'; exists l. now injection H as [= ->].
    - destruct (IH _ H) as (l1 & l2 & H1 & H2).
      exists (x::l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma nth_error_app1 l l' n : n < length l ->
    nth_error (l++l') n = nth_error l n.
  Proof. idtac "nth_error_app1".
    revert l. 
    Time induction n as [|n IHn]; hammer.
  Qed.

  Lemma nth_error_app2 l l' n : length l <= n ->
    nth_error (l++l') n = nth_error l' (n-length l).
  Proof. idtac "nth_error_app2".
    revert l.
    induction n as [|n IHn]; intros [|a l] H; [easy ..|].
    cbn. now apply IHn, Nat.succ_le_mono.
  Qed.

  (** Results directly relating [nth] and [nth_error] *)

  Lemma nth_error_nth : forall (l : list' A) (n : nat) (x d : A),
    nth_error l n = Some x -> nth n l d = x.
  Proof. idtac "nth_error_nth".
    Time hammer.
  Qed.

  Lemma nth_error_nth' : forall (l : list' A) (n : nat) (d : A),
    n < length l -> nth_error l n = Some (nth n l d).
  Proof. idtac "nth_error_nth'".
    Time hammer.
  Qed.

  (******************************)
  (** ** Last element of a list *)
  (******************************)

  (** [last l d] returns the last element of the list [l],
    or the default value [d] if [l] is empty. *)

  Fixpoint last (l:list' A) (d:A) : A :=
  match l with
    | [] => d
    | [a] => a
    | a :: l => last l d
  end.

  Lemma last_last : forall l a d, last (l ++ [a]) d = a.
  Proof. idtac "last_last".
   Time intro l; induction l as [|? l IHl]; hammer.
  Qed.

  (** [removelast l] remove the last element of [l] *)

  Fixpoint removelast (l:list' A) : list' A :=
    match l with
      | [] =>  []
      | [a] => []
      | a :: l => a :: removelast l
    end.

  Lemma app_removelast_last :
    forall l d, l <> [] -> l = removelast l ++ [last l d].
  Proof. idtac "app_removelast_last".
    Time intro l; induction l as [|? l IHl]; hammer.
  Qed.

  Lemma exists_last :
    forall l, l <> [] -> { l' : (list' A) & { a : A | l = l' ++ [a]}}.
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
    Time intro l; induction l as [|? l IHl]; sauto lq:on.
  Qed.

  Lemma removelast_last : forall l a, removelast (l ++ [a]) = l.
  Proof. idtac "removelast_last".
    Time hammer.
  Qed.


  (*****************)
  (** ** Remove    *)
  (*****************)

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Fixpoint remove (x : A) (l : list' A) : list' A :=
    match l with
      | [] => []
      | y::tl => if (eq_dec x y) then remove x tl else y::(remove x tl)
    end.

  Lemma remove_cons : forall x l, remove x (x :: l) = remove x l.
  Proof. idtac "remove_cons". Time hammer. Qed.

  Lemma remove_app : forall x l1 l2,
    remove x (l1 ++ l2) = remove x l1 ++ remove x l2.
  Proof. idtac "remove_app".
   Time intros x l1; induction l1 as [|a l1 IHl1]; hammer.
  Qed.

  Lemma remove_In : forall (l : list' A) (x : A), ~ In x (remove x l).
  Proof. idtac "remove_In".
    Time intro l; induction l as [|x l IHl]; hammer.
  Qed.

  Lemma notin_remove: forall l x, ~ In x l -> remove x l = l.
  Proof. idtac "notin_remove:".
    Time intros l x; induction l as [|y l IHl]; hammer.
  Qed.

  Lemma in_remove: forall l x y, In x (remove y l) -> In x l /\ x <> y.
  Proof. idtac "in_remove:".
    Time intro l; induction l as [|z l IHl]; hammer.
  Qed.

  Lemma in_in_remove : forall l x y, x <> y -> In x l -> In x (remove y l).
  Proof. idtac "in_in_remove".
    Time intro l; induction l as [|z l IHl]; hammer.
  Qed.

  Lemma remove_remove_comm : forall l x y,
    remove x (remove y l) = remove y (remove x l).
  Proof. idtac "remove_remove_comm".
    Time intro l; induction l as [| z l IHl]; hammer.
  Qed.

  Lemma remove_remove_eq : forall l x, remove x (remove x l) = remove x l.
  Proof. idtac "remove_remove_eq". Time hammer.  Qed.

  Lemma remove_length_le : forall l x, length (remove x l) <= length l.
  Proof. idtac "remove_length_le".
    Time intro l; induction l as [|y l IHl]; hammer.
  Qed.

  Lemma remove_length_lt : forall l x, In x l -> length (remove x l) < length l.
  Proof. idtac "remove_length_lt".
    Time intro l; induction l as [|y l IHl]; hammer.
  Qed.


  (******************************************)
  (** ** Counting occurrences of an element *)
  (******************************************)

  Fixpoint count_occ (l : list' A) (x : A) : nat :=
    match l with
      | [] => 0
      | y :: tl =>
        let n := count_occ tl x in
        if eq_dec y x then S n else n
    end.

  (** Compatibility of count_occ with operations on list *)
  Lemma count_occ_In l x : In x l <-> count_occ l x > 0.
  Proof. idtac "count_occ_In".
    Time induction l as [|y l IHl]; hammer.
  Qed.

  Lemma count_occ_not_In l x : ~ In x l <-> count_occ l x = 0.
  Proof. idtac "count_occ_not_In". 
    rewrite count_occ_In. unfold gt. now rewrite Nat.nlt_ge, Nat.le_0_r.
  Qed.

  Lemma count_occ_nil x : count_occ [] x = 0.
  Proof. idtac "count_occ_nil".
   Time hammer.
  Qed.

  Lemma count_occ_inv_nil l :
    (forall x:A, count_occ l x = 0) <-> l = [].
  Proof. idtac "count_occ_inv_nil".
    Time induction l ; hammer.
  Qed.

  Lemma count_occ_cons_eq l x y :
    x = y -> count_occ (x::l) y = S (count_occ l y).
  Proof. idtac "count_occ_cons_eq".
    Time hammer.
  Qed.

  Lemma count_occ_cons_neq l x y :
    x <> y -> count_occ (x::l) y = count_occ l y.
  Proof. idtac "count_occ_cons_neq".
    Time hammer.
  Qed.

  Lemma count_occ_app l1 l2 x :
    count_occ (l1 ++ l2) x = count_occ l1 x + count_occ l2 x.
  Proof. idtac "count_occ_app".
    Time induction l1 ; hammer.
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
    Time hammer.
  Qed.

  Lemma count_occ_bound x l : count_occ l x <= length l.
  Proof. idtac "count_occ_bound".
    Time induction l as [|h l]; hammer.
  Qed.

End Elts.

(*******************************)
(** * Manipulating whole lists *)
(*******************************)

Section ListOps.

  Variable A : Type.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Fixpoint rev (l:list' A) : list' A :=
    match l with
      | [] => []
      | x :: l' => rev l' ++ [x]
    end.

  Lemma rev_app_distr : forall x y:list' A, rev (x ++ y) = rev y ++ rev x.
  Proof. idtac "rev_app_distr".
    intros x y; induction x as [| a l IHl]; cbn.
    - now rewrite app_nil_r.
    - now rewrite IHl, app_assoc.
  Qed.

  Lemma rev_unit : forall (l:list' A) (a:A), rev (l ++ [a]) = a :: rev l.
  Proof. idtac "rev_unit". 
    intros l a. apply rev_app_distr.
  Qed.

  Lemma rev_involutive : forall l:list' A, rev (rev l) = l.
  Proof. idtac "rev_involutive".
    Time intro l; induction l as [| a l IHl]; hammer.
  Qed.

  Lemma rev_eq_app : forall l l1 l2, rev l = l1 ++ l2 -> l = rev l2 ++ rev l1.
  Proof. idtac "rev_eq_app". Time hammer. 
  Qed.

  (*********************************************)
  (** Reverse Induction Principle on Lists     *)
  (*********************************************)

  Lemma rev_list_ind : forall P:list' A-> Prop,
    P [] ->
    (forall (a:A) (l:list' A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list' A, P (rev l).
  Proof. idtac "rev_list_ind".
    Time intros P ? ? l; induction l; hammer.
  Qed.

  Lemma rev_ind : forall P:list' A -> Prop,
    P [] ->
    (forall (x:A) (l:list' A), P l -> P (l ++ [x])) -> forall l:list' A, P l.
  Proof. idtac "rev_ind".
    Time intros P ? ? l; rewrite <- (rev_involutive l).
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
    Time intro l; induction l as [|? l IHl]; hammer.
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
  Qed.


  (**  An alternative tail-recursive definition for reverse *)

  Fixpoint rev_append (l l': list' A) : list' A :=
    match l with
      | [] => l'
      | a::l => rev_append l (a::l')
    end.

  Definition rev' l : list' A := rev_append l [].

  Lemma rev_append_rev : forall l l', rev_append l l' = rev l ++ l'.
  Proof. idtac "rev_append_rev".
    intro l; induction l; simpl; auto; intros.
    rewrite <- app_assoc; firstorder.
  Qed.

  Lemma rev_alt : forall l, rev l = rev_append l [].
  Proof. idtac "rev_alt". Time hammer.
  Qed.

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Fixpoint concat (l : list' (list' A)) : list' A :=
  match l with
  | nil' => nil'
  | cons' x l => x ++ concat l
  end.

  Lemma concat_nil : concat nil' = nil'.
  Proof. idtac "concat_nil".
  Time hammer.
  Qed.

  Lemma concat_cons : forall x l, concat (cons' x l) = x ++ concat l.
  Proof. idtac "concat_cons".
  Time hammer.
  Qed.

  Lemma concat_app : forall l1 l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
  Proof. idtac "concat_app".
  Time intros l1; induction l1 as [|x l1 IH] ; hammer.
  Qed.

  Lemma in_concat : forall l y,
    In y (concat l) <-> exists x, In x l /\ In y x.
  Proof. idtac "in_concat".
    Time intro l; induction l as [|a l IHl]; hammer. 
  Qed.


  (***********************************)
  (** ** Decidable equality on lists *)
  (***********************************)

  Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.

  Lemma list_eq_dec : forall l l':list' A, {l = l'} + {l <> l'}.
  Proof. idtac "list_eq_dec". decide equality. Defined.

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
  Variable f : A -> B.

  Fixpoint map (l:list' A) : list' B :=
    match l with
      | [] => []
      | a :: t => (f a) :: (map t)
    end.

  Lemma map_cons (x:A)(l:list' A) : map (x::l) = (f x) :: (map l).
  Proof. idtac "map_cons".
    Time hammer.
  Qed.

  Lemma in_map :
    forall (l:list' A) (x:A), In x l -> In (f x) (map l).
  Proof. idtac "in_map".
    Time intro l; induction l; hammer.
  Qed.

  Lemma in_map_iff : forall l y, In y (map l) <-> exists x, f x = y /\ In x l.
  Proof. idtac "in_map_iff".
    Time intro l; induction l; hammer.
  Qed.

  Lemma map_length : forall l, length (map l) = length l.
  Proof. idtac "map_length".
    Time intro l; induction l; hammer.
  Qed.

  Lemma map_nth : forall l d n,
    nth n (map l) (f d) = f (nth n l d).
  Proof. idtac "map_nth".
    Time intro l; induction l; hammer.
  Qed.

  Lemma nth_error_map : forall n l,
    nth_error (map l) n = option_map f (nth_error l n).
  Proof. idtac "nth_error_map".
    Time intro n ; induction n as [|n IHn]; hammer.
  Qed.

  Lemma map_nth_error : forall n l d,
    nth_error l n = Some d -> nth_error (map l) n = Some (f d).
  Proof. idtac "map_nth_error".
    Time hammer.
  Qed.

  Lemma map_app : forall l l',
    map (l++l') = (map l)++(map l').
  Proof. idtac "map_app".
    Time intro l; induction l ; hammer.
  Qed.

  Lemma map_last : forall l a,
    map (l ++ [a]) = (map l) ++ [f a].
  Proof. idtac "map_last".
    Time intro l; induction l ; hammer.
  Qed.

  Lemma map_rev : forall l, map (rev l) = rev (map l).
  Proof. idtac "map_rev".
    Time intro l; induction l ; hammer. 
  Qed.

  Lemma map_eq_nil : forall l, map l = [] -> l = [].
  Proof. idtac "map_eq_nil".
    Time hammer.
  Qed.

  Lemma map_eq_cons : forall l l' b,
    map l = b :: l' -> exists a tl, l = a :: tl /\ f a = b /\ map tl = l'.
  Proof. idtac "map_eq_cons".
    Time hammer.
  Qed.

  Lemma map_eq_app  : forall l l1 l2,
    map l = l1 ++ l2 -> exists l1' l2', l = l1' ++ l2' /\ map l1' = l1 /\ map l2' = l2.
  Proof. idtac "map_eq_app ".
    intro l; induction l as [|a l IHl]; simpl; intros l1 l2 Heq.
    - symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; subst.
      exists nil', nil'; repeat split.
    - destruct l1; simpl in Heq; inversion Heq as [[Heq2 Htl]].
      + exists nil', (a :: l); repeat split.
      + destruct (IHl _ _ Htl) as (l1' & l2' & ? & ? & ?); subst.
        exists (a :: l1'), l2'; repeat split.
  Qed.

  (** [map] and count of occurrences *)

  Hypothesis decA: forall x1 x2 : A, {x1 = x2} + {x1 <> x2}.
  Hypothesis decB: forall y1 y2 : B, {y1 = y2} + {y1 <> y2}.
  Hypothesis Hfinjective: forall x1 x2: A, (f x1) = (f x2) -> x1 = x2.

  Lemma count_occ_map x l:
    count_occ decA l x = count_occ decB (map l) (f x).
  Proof. idtac "count_occ_map".
    revert x. Time induction l as [| a l' Hrec]; hammer. Qed.

End Map.

(*****************)
(** ** Flat Map  *)
(*****************)

Section FlatMap.
  Variables (A : Type) (B : Type).
  Variable f : A -> list' B.

    (** [flat_map] *)

    Definition flat_map :=
      fix flat_map (l:list' A) : list' B :=
      match l with
        | nil' => nil'
        | cons' x t => (f x)++(flat_map t)
      end.

    Lemma flat_map_concat_map l :
      flat_map l = concat (map f l).
    Proof. idtac "flat_map_concat_map".
      Time induction l as [|x l IH]; hammer. 
    Qed.

    Lemma flat_map_app l1 l2 :
      flat_map (l1 ++ l2) = flat_map l1 ++ flat_map l2.
    Proof. idtac "flat_map_app".
    now rewrite !flat_map_concat_map, map_app, concat_app.
    Qed.

    Lemma in_flat_map l y :
      In y (flat_map l) <-> exists x, In x l /\ In y (f x).
    Proof. idtac "in_flat_map".
      rewrite flat_map_concat_map, in_concat.
      split.
      - intros [l' [[x [<- ?]] %in_map_iff ?]].
        now exists x.
      - intros [x [? ?]]. exists (f x).
        now split; [apply in_map|].
    Qed.

End FlatMap.

Lemma concat_map : forall A B (f : A -> B) l, map f (concat l) = concat (map (map f) l).
Proof. idtac "concat_map".
  Time intros A B f l; induction l as [|x l IH]; simpl.
  - reflexivity.
  - rewrite map_app, IH; reflexivity.
Qed.

Lemma remove_concat A (eq_dec : forall x y : A, {x = y}+{x <> y}) : forall l x,
  remove eq_dec x (concat l) = flat_map (remove eq_dec x) l.
Proof. idtac "remove_concat".
  intros l x; induction l as [|? ? IHl]; [ reflexivity | simpl ].
  rewrite remove_app, IHl; reflexivity.
Qed.

Lemma map_id : forall (A :Type) (l : list' A),
  map (fun x => x) l = l.
Proof. idtac "map_id".
  Time intros A l; induction l ; hammer.
Qed.

Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
  map g (map f l) = map (fun x => g (f x)) l.
Proof. idtac "map_map".
  Time intros A B C f g l; induction l as [|? ? IHl]; hammer.
Qed.

Lemma map_ext_in :
  forall (A B : Type)(f g:A->B) l, (forall a, In a l -> f a = g a) -> map f l = map g l.
Proof. idtac "map_ext_in".
  Time intros A B f g l; induction l as [|? ? IHl]; hammer.
Qed.

Lemma ext_in_map :
  forall (A B : Type)(f g:A->B) l, map f l = map g l -> forall a, In a l -> f a = g a.
Proof. idtac "ext_in_map". Time intros A B f g l; induction l; hammer. Qed.

Arguments ext_in_map [A B f g l].

Lemma map_ext_in_iff :
   forall (A B : Type)(f g:A->B) l, map f l = map g l <-> forall a, In a l -> f a = g a.
Proof. idtac "map_ext_in_iff". Time hammer. Qed.

Arguments map_ext_in_iff {A B f g l}.

Lemma map_ext :
  forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, map f l = map g l.
Proof. idtac "map_ext".
 Time hammer.
Qed.

Lemma flat_map_ext : forall (A B : Type)(f g : A -> list' B),
  (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
Proof. idtac "flat_map_ext".
  intros A B f g Hext l.
  rewrite 2 flat_map_concat_map.
  now rewrite (map_ext _ g).
Qed.

Lemma nth_nth_nth_map A : forall (l : list' A) n d ln dn, n < length ln \/ length l <= dn ->
  nth (nth n ln dn) l d = nth n (map (fun x => nth x l d) ln) d.
Proof. idtac "nth_nth_nth_map".
  intros l n d ln dn Hlen.
  rewrite <- (map_nth (fun m => nth m l d)).
  destruct Hlen.
  - apply nth_indep. now rewrite map_length.
  - now rewrite (nth_overflow l).
Qed.


(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l:list' B) (a0:A) : A :=
    match l with
      | nil' => a0
      | cons' b t => fold_left t (f a0 b)
    end.

  Lemma fold_left_app : forall (l l':list' B)(i:A),
    fold_left (l++l') i = fold_left l' (fold_left l i).
  Proof. idtac "fold_left_app".
    Time intro l; induction l; hammer.
  Qed.

End Fold_Left_Recursor.

Lemma fold_left_length :
  forall (A:Type)(l:list' A), fold_left (fun x _ => S x) l 0 = length l.
Proof. idtac "fold_left_length".
  intros A l. induction l as [|? ? IH] using rev_ind; [reflexivity|].
  now rewrite fold_left_app, app_length, IH, Nat.add_comm.
Qed.

(************************************)
(** Right-to-left iterator on lists *)
(************************************)

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_right (l:list' B) : A :=
    match l with
      | nil' => a0
      | cons' b t => f b (fold_right t)
    end.

End Fold_Right_Recursor.

  Lemma fold_right_app : forall (A B:Type)(f:A->B->B) l l' i,
    fold_right f i (l++l') = fold_right f (fold_right f i l') l.
  Proof. idtac "fold_right_app".
    Time intros A B f l; induction l; hammer.
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

  Lemma fold_symmetric :
    forall (A : Type) (f : A -> A -> A),
    (forall x y z : A, f x (f y z) = f (f x y) z) ->
    forall (a0 : A), (forall y : A, f a0 y = f y a0) ->
    forall (l : list' A), fold_left f l a0 = fold_right f a0 l.
  Proof. idtac "fold_symmetric".
    intros A f assoc a0 comma0 l.
    induction l as [ | a1 l IHl]; [ simpl; reflexivity | ].
    simpl. rewrite <- IHl. clear IHl. revert a1.
    induction l as [|? ? IHl]; [ auto | ].
    simpl. intro. rewrite <- assoc. rewrite IHl. rewrite IHl. auto.
  Qed.

  (** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
      indexed by elts of [x], sorted in lexicographic order. *)

  Fixpoint list_power (A B:Type)(l:list' A) (l':list' B) :
    list' (list' (A * B)) :=
    match l with
      | nil' => cons' nil' nil'
      | cons' x t =>
	flat_map (fun f:list' (A * B) => map (fun y:B => cons' (x, y) f) l')
        (list_power t l')
    end.


  (*************************************)
  (** ** Boolean operations over lists *)
  (*************************************)

  Section Bool.
    Variable A : Type.
    Variable f : A -> bool.

  (** find whether a boolean function can be satisfied by an
       elements of the list. *)

    Fixpoint existsb (l:list' A) : bool :=
      match l with
      | nil' => false
      | a::l => f a || existsb l
      end.

    Lemma existsb_exists :
      forall l, existsb l = true <-> exists x, In x l /\ f x = true.
    Proof. idtac "existsb_exists".
      Time intro l; induction l as [ | a m IH ]; hammer. 
    Qed.

    Lemma existsb_nth : forall l n d, n < length l ->
      existsb l = false -> f (nth n l d) = false.
    Proof. idtac "existsb_nth".
      Time intro l; induction l as [|a ? IHl]; hammer.
    Qed.

    Lemma existsb_app : forall l1 l2,
      existsb (l1++l2) = existsb l1 || existsb l2.
    Proof. idtac "existsb_app".
      Time intro l1; induction l1 as [|a ? ?]; hammer.
    Qed.

  (** find whether a boolean function is satisfied by
    all the elements of a list. *)

    Fixpoint forallb (l:list' A) : bool :=
      match l with
      | nil' => true
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
      Time intro l1; induction l1 as [|a ? ?]; hammer. 
    Qed.

  (** [filter] *)

    Fixpoint filter (l:list' A) : list' A :=
      match l with
      | nil' => nil'
      | x :: l => if f x then x::(filter l) else filter l
      end.

    Lemma filter_In : forall x l, In x (filter l) <-> In x l /\ f x = true.
    Proof. idtac "filter_In".
      Time intros x l; induction l as [|a ? ?]; hammer.
    Qed.

    Lemma filter_app (l l':list' A) :
      filter (l ++ l') = filter l ++ filter l'.
    Proof. idtac "filter_app".
     Time induction l as [|x l IH]; hammer.
    Qed.

    Lemma concat_filter_map : forall (l : list' (list' A)),
      concat (map filter l) = filter (concat l).
    Proof. idtac "concat_filter_map".
      intro l; induction l as [| v l IHl]; [auto|].
      simpl. rewrite IHl. rewrite filter_app. reflexivity.
    Qed.

  (** [find] *)

    Fixpoint find (l:list' A) : option A :=
      match l with
      | nil' => None
      | x :: tl => if f x then Some x else find tl
      end.

    Lemma find_some l x : find l = Some x -> In x l /\ f x = true.
    Proof. idtac "find_some".
     Time induction l as [|a l IH]; hammer.
    Qed.

    Lemma find_none l : find l = None -> forall x, In x l -> f x = false.
    Proof. idtac "find_none".
     Time induction l as [|a l IH]; hammer.
    Qed.

  (** [partition] *)

    Fixpoint partition (l:list' A) : list' A * list' A :=
      match l with
      | nil' => (nil', nil')
      | x :: tl => let (g,d) := partition tl in
                   if f x then (x::g,d) else (g,x::d)
      end.

  Lemma partition_cons1 a l l1 l2:
    partition l = (l1, l2) ->
    f a = true ->
    partition (a::l) = (a::l1, l2).
  Proof. idtac "partition_cons1".
   Time hammer.
  Qed.

  Lemma partition_cons2 a l l1 l2:
    partition l = (l1, l2) ->
    f a=false ->
    partition (a::l) = (l1, a::l2).
  Proof. idtac "partition_cons2". Time hammer. 
  Qed.

  Lemma partition_length l l1 l2:
    partition l = (l1, l2) ->
    length l = length l1 + length l2.
  Proof. idtac "partition_length".
    revert l1 l2. Time induction l as [ | a l' Hrec]; hammer. Qed.

  Lemma partition_inv_nil (l : list' A):
    partition l = ([], []) <-> l = [].
  Proof. idtac "partition_inv_nil". Time hammer. Qed.

  Lemma elements_in_partition l l1 l2:
    partition l = (l1, l2) ->
    forall x:A, In x l <-> In x l1 \/ In x l2.
  Proof. idtac "elements_in_partition".
    revert l1 l2. Time induction l as [| a l' Hrec]; hammer.
  Qed.

  End Bool.


  (*******************************)
  (** ** Further filtering facts *)
  (*******************************)

  Section Filtering.
    Variables (A : Type).

    Lemma filter_ext_in : forall (f g : A -> bool) (l : list' A),
      (forall a, In a l -> f a = g a) -> filter f l = filter g l.
    Proof. idtac "filter_ext_in".
      intros f g l. Time induction l as [| a l IHl]; hammer.
    Qed.

    Lemma ext_in_filter : forall (f g : A -> bool) (l : list' A),
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

    Lemma filter_ext_in_iff : forall (f g : A -> bool) (l : list' A),
      filter f l = filter g l <-> (forall a, In a l -> f a = g a).
    Proof. idtac "filter_ext_in_iff". Time hammer.
    Qed.

    Lemma filter_map : forall (f g : A -> bool) (l : list' A),
      filter f l = filter g l <-> map f l = map g l.
    Proof. idtac "filter_map".
      intros f g l. now rewrite filter_ext_in_iff, map_ext_in_iff.
    Qed.

    Lemma filter_ext : forall (f g : A -> bool),
      (forall a, f a = g a) -> forall l, filter f l = filter g l.
    Proof. idtac "filter_ext". Time hammer.
    Qed.

    (** Remove by filtering *)

    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

    Definition remove' (x : A) : list' A -> list' A :=
      filter (fun y => if eq_dec x y then false else true).

    Lemma remove_alt (x : A) (l : list' A) : remove' x l = remove eq_dec x l.
    Proof. idtac "remove_alt".
      Time induction l; hammer.
    Qed.

    (** Counting occurrences by filtering *)

    Definition count_occ' (l : list' A) (x : A) : nat :=
      length (filter (fun y => if eq_dec y x then true else false) l).

    Lemma count_occ_alt (l : list' A) (x : A) :
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

    Fixpoint split (l:list' (A*B)) : list' A * list' B :=
      match l with
      | [] => ([], [])
      | (x,y) :: tl => let (left,right) := split tl in (x::left, y::right)
      end.

    Lemma in_split_l : forall (l:list' (A*B))(p:A*B),
      In p l -> In (fst p) (fst (split l)).
    Proof. idtac "in_split_l".
      intro l. Time induction l as [|[? ?] l IHl]; hammer.
    Qed.

    Lemma in_split_r : forall (l:list' (A*B))(p:A*B),
      In p l -> In (snd p) (snd (split l)).
    Proof. idtac "in_split_r".
      intro l. Time induction l as [|[? ?] l IHl]; hammer. Qed.

    Lemma split_nth : forall (l:list' (A*B))(n:nat)(d:A*B),
      nth n l d = (nth n (fst (split l)) (fst d), nth n (snd (split l)) (snd d)).
    Proof. idtac "split_nth".
      Time intro l; induction l as [|a l IHl]; hammer.
    Qed.

    Lemma split_length_l : forall (l:list' (A*B)),
      length (fst (split l)) = length l.
    Proof. idtac "split_length_l".
      Time intro l; induction l ; hammer.
    Qed.

    Lemma split_length_r : forall (l:list' (A*B)),
      length (snd (split l)) = length l.
    Proof. idtac "split_length_r".
     Time intro l; induction l ; hammer.
    Qed.

  (** [combine] is the opposite of [split].
      Lists given to [combine] are meant to be of same length.
      If not, [combine] stops on the shorter list *)

    Fixpoint combine (l : list' A) (l' : list' B) : list' (A*B) :=
      match l,l' with
      | x::tl, y::tl' => (x,y)::(combine tl tl')
      | _, _ => nil'
      end.

    Lemma split_combine : forall (l: list' (A*B)),
      forall l1 l2, split l = (l1, l2) -> combine l1 l2 = l.
    Proof. idtac "split_combine".
     Time intro l; induction l as [|a l IHl]; hammer.
    Qed.

    Lemma combine_split : forall (l:list' A)(l':list' B), length l = length l' ->
      split (combine l l') = (l,l').
    Proof. idtac "combine_split". Time
      Time intro l; induction l ; hammer. Qed.

    Lemma in_combine_l : forall (l:list' A)(l':list' B)(x:A)(y:B),
      In (x,y) (combine l l') -> In x l.
    Proof. idtac "in_combine_l".
     Time intro l; induction l ; hammer.
    Qed.

    Lemma in_combine_r : forall (l:list' A)(l':list' B)(x:A)(y:B),
      In (x,y) (combine l l') -> In y l'.
    Proof. idtac "in_combine_r".
      Time intro l; induction l ; hammer.
    Qed.

    Lemma combine_length : forall (l:list' A)(l':list' B),
      length (combine l l') = min (length l) (length l').
    Proof. idtac "combine_length".
      intro l; induction l; hammer.
    Qed.

    Lemma combine_nth : forall (l:list' A)(l':list' B)(n:nat)(x:A)(y:B),
      length l = length l' ->
      nth n (combine l l') (x,y) = (nth n l x, nth n l' y).
    Proof. idtac "combine_nth".
      Time intro l; induction l; hammer.
    Qed.

  (** [list_prod] has the same signature as [combine], but unlike
     [combine], it adds every possible pairs, not only those at the
     same position. *)

    Fixpoint list_prod (l:list' A) (l':list' B) :
      list' (A * B) :=
      match l with
      | nil' => nil'
      | cons' x t => (map (fun y:B => (x, y)) l')++(list_prod t l')
      end.

    Lemma in_prod_aux :
      forall (x:A) (y:B) (l:list' B),
	In y l -> In (x, y) (map (fun y0:B => (x, y0)) l).
    Proof. idtac "in_prod_aux".
     Time intros x y l; induction l; hammer.
    Qed.

    Lemma in_prod :
      forall (l:list' A) (l':list' B) (x:A) (y:B),
        In x l -> In y l' -> In (x, y) (list_prod l l').
    Proof. idtac "in_prod".
      intro l; induction l;
      [ simpl; tauto
        | simpl; intros l' x y H H0; apply in_or_app; destruct H as [H|H];
          [ left; rewrite H; apply in_prod_aux; assumption | right; auto ] ].
    Qed.

    Lemma in_prod_iff :
      forall (l:list' A)(l':list' B)(x:A)(y:B),
        In (x,y) (list_prod l l') <-> In x l /\ In y l'.
    Proof. idtac "in_prod_iff".
     intros l l' x y; split; [ | intros H; now apply in_prod ].
      induction l as [|a l IHl]; cbn; [easy|].
      intros [[? [[= -> ->] ?]] %in_map_iff|] %in_app_or; tauto.
    Qed.

    Lemma prod_length : forall (l:list' A)(l':list' B),
      length (list_prod l l') = (length l) * (length l').
    Proof. idtac "prod_length".
      intro l; induction l as [|? ? IHl]; simpl; [easy|].
      intros. now rewrite app_length, map_length, IHl.
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

  Definition lel (l m:list' A) := length l <= length m.

  Variables a b : A.
  Variables l m n : list' A.

  Lemma lel_refl : lel l l.
  Proof. idtac "lel_refl". Time hammer.
  Qed.

  Lemma lel_trans : lel l m -> lel m n -> lel l n.
  Proof. idtac "lel_trans". 
    unfold lel; intros.
    now_show (length l <= length n).
    now apply Nat.le_trans with (length m).
  Qed.

  Lemma lel_cons_cons : lel l m -> lel (a :: l) (b :: m).
  Proof. idtac "lel_cons_cons". 
    now intros ? %Nat.succ_le_mono.
  Qed.

  Lemma lel_cons : lel l m -> lel l (b :: m).
  Proof. idtac "lel_cons". Time hammer.
  Qed.

  Lemma lel_tail : lel (a :: l) (b :: m) -> lel l m.
  Proof. idtac "lel_tail". intros. now apply Nat.succ_le_mono.
  Qed.

  Lemma lel_nil : forall l':list' A, lel l' nil' -> nil' = l'.
  Proof. idtac "lel_nil". Time hammer.
  Qed.
End length_order.

#[global]
Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons:
  datatypes.


(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition incl (l m:list' A) := forall a:A, In a l -> In a m.
  #[local]
  Hint Unfold incl : core.

  Lemma incl_nil_l : forall l, incl nil' l.
  Proof. idtac "incl_nil_l". Time hammer.
  Qed.

  Lemma incl_l_nil : forall l, incl l nil' -> l = nil'.
  Proof. idtac "incl_l_nil".
    intro l; destruct l as [|a l]; intros Hincl.
    - reflexivity.
    - exfalso; apply Hincl with a; simpl; auto.
  Qed.

  Lemma incl_refl : forall l:list' A, incl l l.
  Proof. idtac "incl_refl". Time hammer.
  Qed.
  #[local]
  Hint Resolve incl_refl : core.

  Lemma incl_tl : forall (a:A) (l m:list' A), incl l m -> incl l (a :: m).
  Proof. idtac "incl_tl". Time hammer.
  Qed.
  #[local]
  Hint Immediate incl_tl : core.

  Lemma incl_tran : forall l m n:list' A, incl l m -> incl m n -> incl l n.
  Proof. idtac "incl_tran". Time hammer.
  Qed.

  Lemma incl_appl : forall l m n:list' A, incl l n -> incl l (n ++ m).
  Proof. idtac "incl_appl". Time hammer.
  Qed.
  #[local]
  Hint Immediate incl_appl : core. Print incl_appl.

  Lemma incl_appr : forall l m n:list' A, incl l n -> incl l (m ++ n).
  Proof. idtac "incl_appr". Time hammer.
  Qed. 
  #[local]
  Hint Immediate incl_appr : core.

  Lemma incl_cons :
    forall (a:A) (l m:list' A), In a m -> incl l m -> incl (a :: l) m.
  Proof. idtac "incl_cons". Time hammer.
  Qed.
  #[local]
  Hint Resolve incl_cons : core.

  Lemma incl_cons_inv : forall (a:A) (l m:list' A),
    incl (a :: l) m -> In a m /\ incl l m.
  Proof. idtac "incl_cons_inv". Time hammer.
  Qed.

  Lemma incl_app : forall l m n:list' A, incl l n -> incl m n -> incl (l ++ m) n.
  Proof. idtac "incl_app". Time hammer.
  Qed.
  #[local]
  Hint Resolve incl_app : core.

  Lemma incl_app_app : forall l1 l2 m1 m2:list' A,
    incl l1 m1 -> incl l2 m2 -> incl (l1 ++ l2) (m1 ++ m2).
  Proof. idtac "incl_app_app".
    Time hammer.
  Qed.

  Lemma incl_app_inv : forall l1 l2 m : list' A,
    incl (l1 ++ l2) m -> incl l1 m /\ incl l2 m.
  Proof. idtac "incl_app_inv". Time intro l1 ; induction l1 ; hammer.
  Qed.

  Lemma incl_filter f l : incl (filter f l) l.
  Proof. idtac "incl_filter". Time hammer. Qed.

  Lemma remove_incl (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall l1 l2 x,
    incl l1 l2 -> incl (remove eq_dec x l1) (remove eq_dec x l2).
  Proof. idtac "remove_incl". 
    intros l1 l2 x Hincl y Hin.
    apply in_remove in Hin; destruct Hin as [Hin Hneq].
    apply in_in_remove; intuition.
  Qed.

End SetIncl.

Lemma incl_map A B (f : A -> B) l1 l2 : incl l1 l2 -> incl (map f l1) (map f l2).
Proof. idtac "incl_map". 
  intros Hincl x Hinx.
  destruct (proj1 (in_map_iff _ _ _) Hinx) as [y [<- Hiny]].
  now apply in_map, Hincl.
Qed.

#[global]
Hint Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons
  incl_app incl_map: datatypes.


(**************************************)
(** * Cutting a list at some position *)
(**************************************)

Section Cutting.

  Variable A : Type.

  Fixpoint firstn (n:nat)(l:list' A) : list' A :=
    match n with
      | 0 => nil'
      | S n => match l with
		 | nil' => nil'
		 | a::l => a::(firstn n l)
	       end
    end.

  Lemma firstn_nil n: firstn n [] = [].
  Proof. idtac "firstn_nil". Time induction n; hammer. Qed.

  Lemma firstn_cons n a l: firstn (S n) (a::l) = a :: (firstn n l).
  Proof. idtac "firstn_cons". Time hammer. Qed.

  Lemma firstn_all l: firstn (length l) l = l.
  Proof. idtac "firstn_all". Time induction l as [| ? ? H]; hammer. Qed.

  Lemma firstn_all2 n: forall (l:list' A), (length l) <= n -> firstn n l = l.
  Proof. idtac "firstn_all2". Time induction n as [|k iHk] ; hammer.
  Qed.

  Lemma firstn_O l: firstn 0 l = [].
  Proof. idtac "firstn_O". Time hammer. Qed.

  Lemma firstn_le_length n: forall l:list' A, length (firstn n l) <= n.
  Proof. idtac "firstn_le_length".
   Time induction n as [|k iHk]; hammer.
  Qed.

  Lemma firstn_length_le: forall l:list' A, forall n:nat,
    n <= length l -> length (firstn n l) = n.
  Proof. idtac "firstn_length_le:". 
    intro l; induction l as [|x xs Hrec].
    - simpl. intros n H. apply Nat.le_0_r in H. now subst.
    - intro n; destruct n as [|n].
      * now simpl.
      * simpl. intro H. f_equal. apply Hrec. now apply Nat.succ_le_mono.
  Qed.

  Lemma firstn_app n:
    forall l1 l2,
    firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).
  Proof. idtac "firstn_app". Time induction n as [|k iHk]; hammer.
  Qed.

  Lemma firstn_app_2 n:
    forall l1 l2,
    firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.
  Proof. idtac "firstn_app_2". Time induction n as [| k iHk]; hammer.
  Qed.

  Lemma firstn_firstn:
    forall l:list' A,
    forall i j : nat,
    firstn i (firstn j l) = firstn (min i j) l.
  Proof. idtac "firstn_firstn:
   ". Time intro l; induction l as [|x xs Hl]; hammer.
  Qed.

  Fixpoint skipn (n:nat)(l:list' A) : list' A :=
    match n with
      | 0 => l
      | S n => match l with
		 | nil' => nil'
		 | a::l => skipn n l
	       end
    end.

  Lemma firstn_skipn_comm : forall m n l,
  firstn m (skipn n l) = skipn n (firstn (n + m) l).
  Proof. idtac "firstn_skipn_comm". Time intros m n; induction n; hammer. Qed.

  Lemma skipn_firstn_comm : forall m n l,
  skipn m (firstn n l) = firstn (n - m) (skipn m l).
  Proof. idtac "skipn_firstn_comm". now intro m; induction m; intros [] []; simpl; rewrite ?firstn_nil. Qed.

  Lemma skipn_O : forall l, skipn 0 l = l.
  Proof. idtac "skipn_O". Time hammer. Qed.

  Lemma skipn_nil : forall n, skipn n ([] : list' A) = [].
  Proof. idtac "skipn_nil". Time hammer. Qed.

  Lemma skipn_cons n a l: skipn (S n) (a::l) = skipn n l.
  Proof. idtac "skipn_cons". Time hammer. Qed.

  Lemma skipn_all : forall l, skipn (length l) l = nil'.
  Proof. idtac "skipn_all". Time intro l; induction l ; hammer. Qed.

#[deprecated(since="8.12",note="Use skipn_all instead.")] Notation skipn_none := skipn_all.

  Lemma skipn_all2 n: forall l, length l <= n -> skipn n l = [].
  Proof. idtac "skipn_all2". Time hammer.
  Qed.

  Lemma firstn_skipn : forall n l, firstn n l ++ skipn n l = l.
  Proof. idtac "firstn_skipn".
    Time intro n; induction n; hammer.
  Qed.

  Lemma firstn_length : forall n l, length (firstn n l) = min n (length l).
  Proof. idtac "firstn_length".
    Time intro n; induction n; hammer. 
  Qed.

  Lemma skipn_length n :
    forall l, length (skipn n l) = length l - n.
  Proof. idtac "skipn_length".
   Time induction n ; hammer.
  Qed.

  Lemma skipn_app n : forall l1 l2,
    skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
  Proof. idtac "skipn_app". Time induction n; hammer. Qed.

  Lemma firstn_skipn_rev: forall x l,
      firstn x l = rev (skipn (length l - x) (rev l)).
  Proof. idtac "firstn_skipn_rev:".
    intros x l; rewrite <-(firstn_skipn x l) at 3.
    rewrite rev_app_distr, skipn_app, rev_app_distr, rev_length,
            skipn_length, Nat.sub_diag; simpl; rewrite rev_involutive.
    rewrite <-app_nil_r at 1; f_equal; symmetry; apply length_zero_iff_nil.
    repeat rewrite rev_length, skipn_length; apply Nat.sub_diag.
  Qed.

  Lemma firstn_rev: forall x l,
    firstn x (rev l) = rev (skipn (length l - x) l).
  Proof. idtac "firstn_rev:". Time hammer.
  Qed.

  Lemma skipn_rev: forall x l,
      skipn x (rev l) = rev (firstn (length l - x) l).
  Proof. idtac "skipn_rev:".
    intros x l; rewrite firstn_skipn_rev, rev_involutive, <-rev_length.
    destruct (Nat.le_ge_cases (length (rev l)) x) as [L | L].
    - rewrite skipn_all2; [apply Nat.sub_0_le in L | trivial].
      now rewrite L, Nat.sub_0_r, skipn_all.
    - f_equal. now apply Nat.eq_sym, Nat.add_sub_eq_l, Nat.sub_add.
  Qed.

  Lemma removelast_firstn : forall n l, n < length l ->
    removelast (firstn (S n) l) = firstn n l.
  Proof. idtac "removelast_firstn".
   Time intro n; induction n as [|n IHn]; hammer.
  Qed.

  Lemma removelast_firstn_len : forall l,
    removelast l = firstn (pred (length l)) l.
  Proof. idtac "removelast_firstn_len".
    Time intro l; induction l ; hammer.
  Qed.

  Lemma firstn_removelast : forall n l, n < length l ->
    firstn n (removelast l) = firstn n l.
  Proof. idtac "firstn_removelast".
    Time intro n; induction n ; hammer.
  Qed.

End Cutting.

Section CuttingMap.
  Variables A B : Type.
  Variable f : A -> B.

  Lemma firstn_map : forall n l,
      firstn n (map f l) = map f (firstn n l).
  Proof. idtac "firstn_map".
   Time intro n; induction n; hammer.
  Qed.

  Lemma skipn_map : forall n l,
      skipn n (map f l) = map f (skipn n l).
  Proof. idtac "skipn_map".
    Time intro n; induction n; hammer. 
  Qed.
End CuttingMap.

(**************************************************************)
(** ** Combining pairs of lists of possibly-different lengths *)
(**************************************************************)

Section Combining.
    Variables (A B : Type).

    Lemma combine_nil : forall (l : list' A),
      combine l (@nil' B) = @nil' (A*B).
    Proof. idtac "combine_nil".
      intros l. Time hammer.
    Qed.

    Lemma combine_firstn_l : forall (l : list' A) (l' : list' B),
      combine l l' = combine l (firstn (length l) l').
    Proof. idtac "combine_firstn_l".
      Time intro l; induction l as [| x l IHl]; hammer.
    Qed.

    Lemma combine_firstn_r : forall (l : list' A) (l' : list' B),
      combine l l' = combine (firstn (length l') l) l'.
    Proof. idtac "combine_firstn_r".
    intros l l'. generalize dependent l.
     Time induction l' as [| x' l' IHl']; hammer.
    Qed.

    Lemma combine_firstn : forall (l : list' A) (l' : list' B) (n : nat),
      firstn n (combine l l') = combine (firstn n l) (firstn n l').
    Proof. idtac "combine_firstn".
     Time intro l; induction l as [| x l IHl]; hammer.
    Qed.

End Combining.

(**********************************************************************)
(** ** Predicate for List addition/removal (no need for decidability) *)
(**********************************************************************)

Section Add.

  Variable A : Type.

  (* [Add a l l'] means that [l'] is exactly [l], with [a] added
     once somewhere *)
  Inductive Add (a:A) : list' A -> list' A -> Prop :=
    | Add_head l : Add a l (a::l)
    | Add_cons x l l' : Add a l l' -> Add a (x::l) (x::l').

  Lemma Add_app a l1 l2 : Add a (l1++l2) (l1++a::l2).
  Proof. idtac "Add_app".
  Time induction l1; hammer.
  Qed.

  Lemma Add_split a l l' :
    Add a l l' -> exists l1 l2, l = l1++l2 /\ l' = l1++a::l2.
  Proof. idtac "Add_split".
   induction 1 as [l|x ? ? ? IHAdd].
   - exists nil'; exists l; split; trivial.
   - destruct IHAdd as (l1 & l2 & Hl & Hl').
     exists (x::l1); exists l2; split; simpl; f_equal; trivial.
  Qed.

  Lemma Add_in a l l' : Add a l l' ->
   forall x, In x l' <-> In x (a::l).
  Proof. idtac "Add_in".
   Time induction 1 as [|? ? ? ? IHAdd]; hammer. 
  Qed.

  Lemma Add_length a l l' : Add a l l' -> length l' = S (length l).
  Proof. idtac "Add_length".
  Time induction 1; hammer.
  Qed.

  Lemma Add_inv a l : In a l -> exists l', Add a l' l.
  Proof. idtac "Add_inv".
   Time hammer.
  Qed.

  Lemma incl_Add_inv a l u v :
    ~In a l -> incl (a::l) v -> Add a u v -> incl l u.
  Proof. idtac "incl_Add_inv".
   Time hammer.
  Qed.

End Add.

(********************************)
(** ** Lists without redundancy *)
(********************************)

Section ReDun.

  Variable A : Type.

  Inductive NoDup : list' A -> Prop :=
    | NoDup_nil : NoDup nil'
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
  Proof. idtac "NoDup_remove". Time hammer.
  Qed.

  Lemma NoDup_remove_1 l l' a : NoDup (l++a::l') -> NoDup (l++l').
  Proof. idtac "NoDup_remove_1". Time hammer.
  Qed.

  Lemma NoDup_remove_2 l l' a : NoDup (l++a::l') -> ~In a (l++l').
  Proof. idtac "NoDup_remove_2". Time hammer.
  Qed.

  Lemma NoDup_cons_iff a l:
    NoDup (a::l) <-> ~ In a l /\ NoDup l.
  Proof. idtac "NoDup_cons_iff". Time hammer.
  Qed.

  Lemma NoDup_rev l : NoDup l -> NoDup (rev l).
  Proof. idtac "NoDup_rev".
    induction l as [|a l IHl]; simpl; intros Hnd; [ constructor | ].
    inversion_clear Hnd as [ | ? ? Hnin Hndl ].
    assert (Add a (rev l) (rev l ++ a :: nil')) as Hadd
      by (rewrite <- (app_nil_r (rev l)) at 1; apply Add_app).
    apply NoDup_Add in Hadd; apply Hadd; intuition.
    now apply Hnin, in_rev.
  Qed.

  Lemma NoDup_filter f l : NoDup l -> NoDup (filter f l).
  Proof. idtac "NoDup_filter".
    Time induction l as [|a l IHl]; hammer.
  Qed.

  (** Effective computation of a list without duplicates *)

  Hypothesis decA: forall x y : A, {x = y} + {x <> y}.

  Fixpoint nodup (l : list' A) : list' A :=
    match l with
      | [] => []
      | x::xs => if in_dec decA x xs then nodup xs else x::(nodup xs)
    end.

  Lemma nodup_fixed_point (l : list' A) :
    NoDup l -> nodup l = l.
  Proof. idtac "nodup_fixed_point".
    Time induction l as [| x l IHl]; hammer.
  Qed.

  Lemma nodup_In l x : In x (nodup l) <-> In x l.
  Proof. idtac "nodup_In".
    Time induction l as [|a l' Hrec]; hammer.
  Qed.

  Lemma nodup_incl l1 l2 : incl l1 (nodup l2) <-> incl l1 l2.
  Proof. idtac "nodup_incl". Time hammer.
  Qed.

  Lemma NoDup_nodup l: NoDup (nodup l). (* The tactic wants an inhabitant here *)
  Proof. idtac "NoDup_nodup".
    induction l as [|a l' Hrec]; simpl.
    - constructor.
    - destruct (in_dec decA a l'); simpl.
      * assumption.
      * constructor; [ now rewrite nodup_In | assumption].
  Qed.

  Lemma nodup_inv k l a : nodup k = a :: l -> ~ In a l.
  Proof. idtac "nodup_inv". Time hammer.
  Qed.

  Lemma NoDup_count_occ l:
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

  Lemma NoDup_count_occ' l:
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
        assert (n < length l) by (now rewrite <- nth_error_Some, Hn).
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

  Lemma NoDup_incl_NoDup (l l' : list' A) : NoDup l ->
    length l' <= length l -> incl l l' -> NoDup l'.
  Proof. idtac "NoDup_incl_NoDup".
    revert l'; induction l as [|a l IHl]; simpl; intros l' Hnd Hlen Hincl.
    - now destruct l'; inversion Hlen.
    - assert (In a l') as Ha by now apply Hincl; left.
      apply in_split in Ha as [l1' [l2' ->]].
      inversion_clear Hnd as [|? ? Hnin Hnd'].
      apply (NoDup_Add (Add_app a l1' l2')); split.
      + apply IHl; auto.
        * rewrite app_length.
          rewrite app_length in Hlen; simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
          now apply Nat.succ_le_mono.
        * apply (incl_Add_inv (u:= l1' ++ l2')) in Hincl; auto.
          apply Add_app.
      + intros Hnin'.
        assert (incl (a :: l) (l1' ++ l2')) as Hincl''.
        { apply incl_tran with (l1' ++ a :: l2'); auto.
          intros x Hin.
          apply in_app_or in Hin as [Hin|[->|Hin]]; intuition. }
        apply NoDup_incl_length in Hincl''; [ | now constructor ].
        apply (Nat.nle_succ_diag_l (length l1' + length l2')).
        rewrite_all app_length.
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
 intro H. now apply (in_map f) in H.
Qed.

(***********************************)
(** ** Sequence of natural numbers *)
(***********************************)

Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

  Fixpoint seq (start len:nat) : list' nat :=
    match len with
      | 0 => nil'
      | S len => start :: seq (S start) len
    end.

  Lemma cons_seq : forall len start, start :: seq (S start) len = seq start (S len).
  Proof. idtac "cons_seq".
    Time hammer.
  Qed.

  Lemma seq_length : forall len start, length (seq start len) = len.
  Proof. idtac "seq_length".
    Time intro len; induction len; hammer.
  Qed.

  Lemma seq_nth : forall len start n d,
    n < len -> nth n (seq start len) d = start+n.
  Proof. idtac "seq_nth".
    Time intro len; induction len as [|len IHlen]; hammer. 
  Qed.

  Lemma seq_shift : forall len start,
    map S (seq start len) = seq (S start) len.
  Proof. idtac "seq_shift".
    Time intro len; induction len as [|len IHlen]; hammer. 
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

End NatSeq.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Prop.

    Inductive Exists : list' A -> Prop :=
      | Exists_cons_hd : forall x l, P x -> Exists (x::l)
      | Exists_cons_tl : forall x l, Exists l -> Exists (x::l).

    #[local]
    Hint Constructors Exists : core.

    Lemma Exists_exists (l:list' A) :
      Exists l <-> (exists x, In x l /\ P x).
    Proof. idtac "Exists_exists". 
      split.
      - Time induction 1; hammer.
      - Time induction l; hammer.
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
        apply nth_In; assumption.
        assumption.
    Qed.

    Lemma Exists_nil : Exists nil' <-> False.
    Proof. idtac "Exists_nil". Time hammer. Qed.

    Lemma Exists_cons x l:
      Exists (x::l) <-> P x \/ Exists l.
    Proof. idtac "Exists_cons". Time hammer. Qed.

    Lemma Exists_app l1 l2 :
      Exists (l1 ++ l2) <-> Exists l1 \/ Exists l2.
    Proof. idtac "Exists_app".
      Time induction l1; hammer.
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
    Defined.

    Lemma Exists_fold_right l :
      Exists l <-> fold_right (fun x => or (P x)) False l.
    Proof. idtac "Exists_fold_right".
      Time induction l; hammer. 
    Qed.

    Lemma incl_Exists l1 l2 : incl l1 l2 -> Exists l1 -> Exists l2.
    Proof. idtac "incl_Exists". Time hammer.
    Qed.

    Inductive Forall : list' A -> Prop :=
      | Forall_nil : Forall nil'
      | Forall_cons : forall x l, P x -> Forall l -> Forall (x::l).

    #[local]
    Hint Constructors Forall : core.

    Lemma Forall_inv : forall (a:A) l, Forall (a :: l) -> P a.
    Proof. idtac "Forall_inv". Time hammer.
    Qed.

    Lemma Forall_inv_tail : forall (a:A) l, Forall (a :: l) -> Forall l.
    Proof. idtac "Forall_inv_tail". Time hammer.
    Qed.

    Lemma Forall_nil_iff : Forall [] <-> True.
    Proof. idtac "Forall_nil_iff". Time hammer.
    Qed.

    Lemma Forall_cons_iff : forall (a:A) l, Forall (a :: l) <-> P a /\ Forall l.
    Proof. idtac "Forall_cons_iff". Time hammer.
    Qed.

    Lemma Forall_forall (l:list' A):
      Forall l <-> (forall x, In x l -> P x).
    Proof. idtac "Forall_forall". 
      split.
      - Time induction 1; hammer. 
      - Time induction l; hammer. 
    Qed.

    Lemma Forall_nth l :
      Forall l <-> forall i d, i < length l -> P (nth i l d).
    Proof. idtac "Forall_nth". 
      split.
      - intros HF i d Hl.
        apply (Forall_forall l).
        assumption.
        apply nth_In; assumption.
      - intros HF.
        apply Forall_forall; intros a Hin.
        apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
        rewrite <- Heq; intuition.
    Qed.

    Lemma Forall_app l1 l2 :
      Forall (l1 ++ l2) <-> Forall l1 /\ Forall l2.
    Proof. idtac "Forall_app".
      Time induction l1 as [|a l1 IH]; hammer.
    Qed.

    Lemma Forall_elt a l1 l2 : Forall (l1 ++ a :: l2) -> P a.
    Proof. idtac "Forall_elt". Time hammer.
    Qed.

    Lemma Forall_rev l : Forall l -> Forall (rev l).
    Proof. idtac "Forall_rev".
      Time induction l; hammer.
    Qed.

    Lemma Forall_rect : forall (Q : list' A -> Type),
      Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, Forall l -> Q l.
    Proof. idtac "Forall_rect".
      intros Q H H' l; induction l; intro; [|eapply H', Forall_inv]; eassumption.
    Qed.

    Lemma Forall_dec :
      (forall x:A, {P x} + { ~ P x }) ->
      forall l:list' A, {Forall l} + {~ Forall l}.
    Proof. idtac "Forall_dec".
      intros Pdec l. induction l as [|a l' Hrec].
      - left. apply Forall_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Defined.

    Lemma Forall_fold_right l :
      Forall l <-> fold_right (fun x => and (P x)) True l.
    Proof. idtac "Forall_fold_right".
      Time induction l; hammer. 
    Qed.

    Lemma incl_Forall l1 l2 : incl l2 l1 -> Forall l1 -> Forall l2.
    Proof. idtac "incl_Forall". Time hammer.
    Qed.

  End One_predicate.

  Lemma map_ext_Forall B : forall (f g : A -> B) l,
    Forall (fun x => f x = g x) l -> map f l = map g l.
  Proof. idtac "map_ext_Forall".
    intros; apply map_ext_in, Forall_forall; assumption.
  Qed.

  Lemma Exists_impl : forall (P Q : A -> Prop), (forall a : A, P a -> Q a) ->
    forall l, Exists P l -> Exists Q l.
  Proof. idtac "Exists_impl".
    Time intros P Q H l H0;
    induction H0 as [x l H0|x l H0 IHExists]; hammer.
  Qed.

  Lemma Exists_or : forall (P Q : A -> Prop) l,
    Exists P l \/ Exists Q l -> Exists (fun x => P x \/ Q x) l.
  Proof. idtac "Exists_or".
    Time intros P Q l; induction l as [|a l IHl]; hammer.
  Qed.

  Lemma Exists_or_inv : forall (P Q : A -> Prop) l,
    Exists (fun x => P x \/ Q x) l -> Exists P l \/ Exists Q l.
  Proof. idtac "Exists_or_inv".
    Time intros P Q l; induction l as [|a l IHl]; hammer.
  Qed.

  Lemma Forall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
    forall l, Forall P l -> Forall Q l.
  Proof. idtac "Forall_impl". Time hammer.
  Qed.

  Lemma Forall_and : forall (P Q : A -> Prop) l,
    Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
  Proof. idtac "Forall_and".
   Time intros P Q l; induction l; hammer. Qed.

  Lemma Forall_and_inv : forall (P Q : A -> Prop) l,
    Forall (fun x => P x /\ Q x) l -> Forall P l /\ Forall Q l.
  Proof. idtac "Forall_and_inv".
    Time intros P Q l; induction l; hammer. 
  Qed.

  Lemma Forall_Exists_neg (P:A->Prop)(l:list' A) :
    Forall (fun x => ~ P x) l <-> ~(Exists P l).
  Proof. idtac "Forall_Exists_neg".
    rewrite Forall_forall, Exists_exists. firstorder.
  Qed.

  Lemma Exists_Forall_neg (P:A->Prop)(l:list' A) :
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

  Lemma neg_Forall_Exists_neg (P:A->Prop) (l:list' A) :
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
    forall l:list' A,
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
Proof. idtac "Exists_map". Time
  induction l as [|a l IHl]; hammer.
Qed.

Lemma Exists_concat A P (ls : list' (list' A)) :
  Exists P (concat ls) <-> Exists (Exists P) ls.
Proof. idtac "Exists_concat".
  induction ls as [|l ls IHls].
  - cbn. now rewrite Exists_nil.
  - cbn. now rewrite Exists_app, Exists_cons, IHls.
Qed.

Lemma Exists_flat_map A B P ls (f : A -> list' B) :
  Exists P (flat_map f ls) <-> Exists (fun d => Exists P (f d)) ls.
Proof. idtac "Exists_flat_map".
  now rewrite flat_map_concat_map, Exists_concat, Exists_map.
Qed.

Lemma Forall_map A B (f : A -> B) P l :
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof. idtac "Forall_map".
  Time induction l as [|a l IHl]; hammer.
Qed.

Lemma Forall_concat A P (ls : list' (list' A)) :
  Forall P (concat ls) <-> Forall (Forall P) ls.
Proof. idtac "Forall_concat".
  induction ls as [|l ls IHls]; cbn.
  - now rewrite !Forall_nil_iff.
  - now rewrite Forall_app, Forall_cons_iff, IHls.
Qed.

Lemma Forall_flat_map A B P ls (f : A -> list' B) :
  Forall P (flat_map f ls) <-> Forall (fun d => Forall P (f d)) ls.
Proof. idtac "Forall_flat_map".
  now rewrite flat_map_concat_map, Forall_concat, Forall_map.
Qed.

Lemma exists_Forall A B : forall (P : A -> B -> Prop) l,
  (exists k, Forall (P k) l) -> Forall (fun x => exists k, P k x) l.
Proof. idtac "exists_Forall".
  Time intros P l; induction l as [|a l IHl]; hammer.
Qed.

Lemma Forall_image A B : forall (f : A -> B) l,
  Forall (fun y => exists x, y = f x) l <-> exists l', l = map f l'.
Proof. idtac "Forall_image".
  intros f l; induction l as [|a l IHl]; split; intros HF.
  - exists nil'; reflexivity.
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

Lemma concat_nil_Forall A : forall (l : list' (list' A)),
  concat l = nil' <-> Forall (fun x => x = nil') l.
Proof. idtac "concat_nil_Forall".
  intro l; induction l as [|a l IHl]; simpl; split; intros Hc; auto.
  - apply app_eq_nil in Hc.
    constructor; firstorder.
  - inversion Hc; subst; simpl.
    now apply IHl.
Qed.

Lemma in_flat_map_Exists A B : forall (f : A -> list' B) x l,
  In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
Proof. idtac "in_flat_map_Exists".
  intros f x l; rewrite in_flat_map.
  split; apply Exists_exists.
Qed.

Lemma notin_flat_map_Forall A B : forall (f : A -> list' B) x l,
  ~ In x (flat_map f l) <-> Forall (fun y => ~ In x (f y)) l.
Proof. idtac "notin_flat_map_Forall".
  intros f x l; rewrite Forall_Exists_neg.
  apply not_iff_compat, in_flat_map_Exists.
Qed.


Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Prop.

  Inductive Forall2 : list' A -> list' B -> Prop :=
    | Forall2_nil : Forall2 [] []
    | Forall2_cons : forall x y l l',
      R x y -> Forall2 l l' -> Forall2 (x::l) (y::l').

  #[local]
  Hint Constructors Forall2 : core.

  Lemma Forall2_refl : Forall2 [] [].
  Proof. idtac "Forall2_refl". Time hammer. Qed.

  Lemma Forall2_app_inv_l : forall l1 l2 l',
    Forall2 (l1 ++ l2) l' ->
    exists l1' l2', Forall2 l1 l1' /\ Forall2 l2 l2' /\ l' = l1' ++ l2'.
  Proof. idtac "Forall2_app_inv_l".
    Time intro l1; induction l1 as [|a l1 IHl1]; hammer.
  Qed.

  Lemma Forall2_app_inv_r : forall l1' l2' l,
    Forall2 l (l1' ++ l2') ->
    exists l1 l2, Forall2 l1 l1' /\ Forall2 l2 l2' /\ l = l1 ++ l2.
  Proof. idtac "Forall2_app_inv_r".
    Time intro l1'; induction l1' as [|a l1' IHl1']; hammer.
  Qed.

  Lemma Forall2_app : forall l1 l2 l1' l2',
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

  Inductive ForallOrdPairs : list' A -> Prop :=
    | FOP_nil : ForallOrdPairs nil'
    | FOP_cons : forall a l,
      Forall (R a) l -> ForallOrdPairs l -> ForallOrdPairs (a::l).

  #[local]
  Hint Constructors ForallOrdPairs : core.

  Lemma ForallOrdPairs_In : forall l,
    ForallOrdPairs l ->
    forall x y, In x l -> In y l -> x=y \/ R x y \/ R y x.
  Proof. idtac "ForallOrdPairs_In".
    Time induction 1; hammer.
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
  Proof. idtac "ForallOrdPairs_ForallPairs". Time hammer.
  Qed.
End ForallPairs.

Section Repeat.

  Variable A : Type.
  Fixpoint repeat (x : A) (n: nat ) :=
    match n with
      | O => []
      | S k => x::(repeat x k)
    end.

  Lemma repeat_length x n:
    length (repeat x n) = n.
  Proof. idtac "repeat_length". Time induction n ; hammer.
  Qed.

  Lemma repeat_spec n x y:
    In y (repeat x n) -> y=x.
  Proof. idtac "repeat_spec". Time induction n ; hammer.
  Qed.

  Lemma repeat_cons n a :
    a :: repeat a n = repeat a n ++ (a :: nil').
  Proof. idtac "repeat_cons".
    Time induction n as [|n IHn]; hammer.
  Qed.

  Lemma repeat_app x n m :
    repeat x (n + m) = repeat x n ++ repeat x m.
  Proof. idtac "repeat_app". Time induction n ; hammer.
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
    Time induction l as [|a l IHl]; hammer.
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
  Proof. idtac "count_occ_repeat_neq". Time induction n ; hammer.
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

  Lemma count_occ_sgt l x : l = x :: nil' <->
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
    revert n. Time induction m as [|m IHm] ; hammer.
  Qed.

  Lemma nth_error_repeat a m n :
    n < m -> nth_error (repeat a m) n = Some a.
  Proof. idtac "nth_error_repeat". 
    intro Hnm. rewrite (nth_error_nth' _ a).
    - now rewrite nth_repeat.
    - now rewrite repeat_length.
  Qed.

End Repeat.

Lemma repeat_to_concat A n (a:A) :
  repeat a n = concat (repeat [a] n).
Proof. idtac "repeat_to_concat". Time induction n ; hammer.
Qed.


(** Sum of elements of a list of [nat]: [list_sum] *)

Definition list_sum l := fold_right plus 0 l.

Lemma list_sum_app : forall l1 l2,
   list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof. idtac "list_sum_app". Time intro l1 ; induction l1 ; hammer.
Qed.

(** Max of elements of a list of [nat]: [list_max] *)

Definition list_max l := fold_right max 0 l.

Lemma list_max_app : forall l1 l2,
   list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
Proof. idtac "list_max_app".
Time intro l1; induction l1 as [|a l1 IHl1]; hammer. 
Qed.

Lemma list_max_le : forall l n,
  list_max l <= n <-> Forall (fun k => k <= n) l.
Proof. idtac "list_max_le".
 Time intro l; induction l as [|a l IHl]; hammer.
Qed.

Lemma list_max_lt : forall l n, l <> nil' ->
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
