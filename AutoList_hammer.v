Require Setoid.
Require Import BinInt.
Require Import PeanoNat Le Gt Minus Bool Lt.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.

(** Polymorphic list's and some operations *)

#[universes(template)]
Inductive list' (A : Type) : Type :=
 | nil : list' A
 | cons : A -> list' A -> list' A.

Arguments nil {A}.
Arguments cons {A} a l.

Declare Scope list'_scope.
Delimit Scope list'_scope with list'.
Bind Scope list'_scope with list'.

Infix "::" := cons (at level 60, right associativity) : list'_scope.


Local Open Scope list'_scope.

Set Implicit Arguments. 


Open Scope list'_scope.

(** Standard notations for list's.
In a special module to avoid conflicts. *)
Module List'Notations.
Notation "[ ]" := nil (format "[ ]") : list'_scope.
Notation "[ x ]" := (cons x nil) : list'_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list'_scope.
End List'Notations.

Import List'Notations.

Section Lists'.


Definition length (A : Type) : list' A -> nat :=
  fix length l :=
  match l with
   | nil => O
   | _ :: l' => S (length l')
  end.

(** Concatenation of two list's *)

Definition app (A : Type) : list' A -> list' A -> list' A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : list'_scope.


  Variable A : Type.
  Variable a_0 : A.
 (*  Variable Hnat : CompDec nat.
  Variable Hbool : CompDec bool. *)
  (* Variable HOpA : CompDec (option A). *)
  (* Variable HlA : CompDec (list' A). *)

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
      | [] => nil
      | a :: m => m
    end.

  (** The [In] predicate *)
  Fixpoint In (a:A) (l:list' A) : Prop :=
    match l with
      | [] => False
      | b :: m => (eq a b) \/ (In a m)
    end.



  (** *** Generic facts *)

  (** Discrimination *)
  Theorem nil_cons : forall (x:A) (l:list' A), [] <> x :: l.
  Proof. hammer.
  Qed.


  (** Destruction *)

  Theorem destruct_list' : forall l : list' A, {x:A & {tl:list' A | l = x::tl}}+{l = []}.
  Proof.
    hammer.
  Qed.

  Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof.
 hammer.
Qed.



  Lemma hd_error_some_nil : forall l (a:A), hd_error l = Some a -> l <> nil.
  Proof. 
  hammer.
   Qed.


  Theorem length_zero_iff_nil (l : list' A):
   length l <> 0 <-> l <> nil.
  Proof. hammer.
  Qed.

  (** *** Head and tail *)

  Theorem hd_error_nil : hd_error (@nil A) = None.
Proof.
hammer.
  Qed.


  (************************)
  (** *** Facts about [In] *)
  (************************)


  (** Characterization of [In] *)

  Theorem in_eq : forall (a:A) (l:list' A), In a (a :: l).
  Proof.
  hammer.
  Qed.

  Theorem in_cons : forall (a b:A) (l:list' A), In b l -> In b (a :: l).
  Proof.
  hammer. 
  Qed.

  Theorem not_in_cons (x a : A) (l : list' A):
    ~ In x (a::l) <-> x<>a /\ ~ In x l.
  Proof.
  hammer.
  Qed.

  Theorem in_nil : forall a:A, ~ In a nil.
  Proof.
  hammer.
  Qed.

  Theorem in_split : forall x (l:list' A), In x l-> exists l1 l2, l = l1++x::l2.
  Proof.
  (* induction l ; hammer. ==> fails *) 
Admitted.

  (** Inversion *)
  Lemma in_inv : forall (a b:A) (l:list' A), In b (a :: l) -> a = b \/ In b l.
  Proof.
  hammer.
  Qed.



  (**************************)
  (** *** Facts about [app] *)
  (**************************)
Print app.


  (** Discrimination *)
  Theorem app_cons_not_nil : forall (x y:list' A) (a:A), nil <> ((a :: y) ++ x).
  Proof.
  hammer.
  Qed.


  (** Concat with [nil] *)
  Theorem app_nil_l : forall l:list' A, [] ++ l = l.
  Proof.
   hammer.
  Qed.

  Theorem app_nil_r' : forall l:list' A, l ++ [] = l.
  Proof.
  induction l ; hammer.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Theorem app_nil_end : forall (l:list' A), l = l ++ [].
  Proof. hammer. Qed. 



  (** [app] is associative *)
  Theorem app_assoc : forall l m n:list' A, (l ++ m ++ n) = ((l ++ m) ++ n).
  Proof.
  induction l ; hammer.
  Qed. 

  (* begin hide *)
  (* Deprecated *)

  Theorem app_assoc_reverse : forall l m n:list' A, ((l ++ m) ++ n) = (l ++ m ++ n).
  Proof.
  hammer.
  Qed.

  Hint Resolve app_assoc_reverse : core.
  (* end hide *)

  (** [app] commutes with [cons] *)
  Theorem app_comm_cons : forall (x y:list' A) (a:A), (a :: (x ++ y)) = ((a :: x) ++ y).
  Proof.
  hammer.
  Qed.

  (** Facts deduced from the result of a concatenation *)

  Theorem app_eq_nil : forall l l':list' A, 
(l ++ l') = nil -> l = nil /\ l' = nil.
  Proof.
   destruct l ; destruct l' ; hammer. Qed.

   Theorem app_eq_unit :
    forall (x y:list' A) (a:A),
      x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil.
  Proof.
  hammer.
  Qed.

  Lemma app_inj_tail :
    forall (x y:list' A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof.
 induction x as [| x l IHl];
      [ destruct y as [| a l] | destruct y as [| a l0] ]. (* hammer cannot reconstruct the proof *) 
    - hammer.
    - (*  hammer. *) admit.
    - (*  hammer. *) admit. 
    - hammer. 
Admitted.

  (** Compatibility with other operations *)

  Lemma app_length : forall l l' : list' A, length (l++l') = length l + length l'.
  Proof.
    induction l; hammer. Qed.