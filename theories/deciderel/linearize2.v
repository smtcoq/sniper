Require Import List.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Checker.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
Import ListNotations MCMonadNotation.

(** Specification of this file: 
giving an inductive relation I of (implicit) parameters A1, ... Aj,
and of arity l (parameters excluded)
with constructors c_i of type 
forall (xi1 : Bi1), ..., (xin : Bin), 
Pi1 xi1 ... xin -> ... -> Pik xi1 ... xin ->
I (fi1 xi1 ... xin) ... (fil xi1 ... xin),
we linearize the conclusion I (f1 xi1 ... xin) ... (fl xi1 ... xin), which means that we remove 
all the duplicates among the xis and all mentions of A1, ... Aj 
at an index position 
We suppose that all the Pis are inductive relations with no higher-order or dependent types
We suppose that all the functions fis are only made of applied constructors or functions 
and do not depend on each other
All the types Bi1, ... Bin should be datatypes or types variables
and they are not dependent types

Let us take an example with the addition written in a relational way:

Inductive add : nat -> nat -> nat -> Prop :=
| add0 : forall n, add 0 n n
| addS : forall n m k, add n m k -> add (S n) m (S k).

The plugin constructs:

Inductive add_linear : nat -> nat -> nat -> Prop :=
| add0_linear : forall n n', n = n' -> add_linear 0 n n
| addS_linear : forall n m k, add_linear n m k -> add_linear (S n) m (S k).

The linearization can be made in two ways: 
- linearize_default_eq will add propositionnal equalities between the fresh variables
- linearize_bool_eq will add boolean equalities between the fresh variables. 
It should be used with an environment registering (possibly parametric) boolean equalities for 
all the arguments. Whenever a decidable equality should occur on a type variable, 
it will scan the parameters of the inductive to see if one of it is a hypothesis of decidablity

Let us take another example :

Inductive Add (A : Type) (a : A) : list A -> list A -> Prop :=
    Add_head : forall l : list A, Add a l (a :: l)
  | Add_cons : forall (x : A) (l l' : list A),
               Add a l l' -> Add a (x :: l) (x :: l').

The default linearization is the only one to work without further assumptions 
(or without instantiating the A) because we need a decidable equality on A.
But if we consider:

Inductive Add' (A : Type) (HA : has_boolean_eq A) (a : A) : list A -> list A -> Prop :=
    Add_head' : forall l : list A, Add' HA a l (a :: l)
  | Add_cons' : forall (x : A) (l l' : list A),
               Add' HA a l l' -> Add' HA a (x :: l) (x :: l').

Then we get:

Inductive Add'_linear (A : Type) (HA: has_boolean_eq A) (a : A) : list A -> list A -> Prop :=
    Add_head'_linear : forall l l' : list A, eq_dec A a a' -> eq_dec ((fun x (Hx : eq_dec x)
=> eq_dec (list x)) A HA) l l' ->
 Add'_linear a l (a' :: l')
  | Add_cons'_linear : forall (x  x' : A) (l l' : list A), eq_dec HA x x' ->
               Add'_linear a l l' -> Add'_linear a (x :: l) (x :: l').

 *)

Section map_predicate_shift.
  Context {T : Type}.
  Context (fn : (nat -> T) -> term -> term).
  Context (shift : nat -> (nat -> T) -> nat -> T).
  Context (finst : Instance.t -> Instance.t).
  Context (f : nat -> T).

  Definition map_predicate_shift (p : predicate term) :=
    {| pparams := map (fn f) p.(pparams);
        puinst := finst p.(puinst);
        pcontext := p.(pcontext);
        preturn := fn (shift #|p.(pcontext)| f) p.(preturn) |}.

(*   Lemma map_shift_pparams (p : predicate term) :
    map (fn f) (pparams p) = pparams (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_preturn (p : predicate term) :
    fn (shift #|p.(pcontext)| f) (preturn p) = preturn (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_pcontext (p : predicate term) :
    (pcontext p) =
    pcontext (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_puinst (p : predicate term) :
    finst (puinst p) = puinst (map_predicate_shift p).
  Proof using Type. reflexivity. Qed. *)
  
End map_predicate_shift. 

Section map_branch_shift.
  Context {T : Type}.
  Context (fn : (nat -> T) -> term -> term).
  Context (shift : nat -> (nat -> T) -> nat -> T).
  Context (f : nat -> T).

  Definition map_branch_shift (b : branch term) :=
  {| bcontext := b.(bcontext);
      bbody := fn (shift #|b.(bcontext)| f) b.(bbody) |}.

(*   Lemma map_shift_bbody (b : branch term) :
    fn (shift #|b.(bcontext)| f) (bbody b) = bbody (map_branch_shift b).
  Proof using Type. reflexivity. Qed.
  
  Lemma map_shift_bcontext (b : branch term) :
    (bcontext b) = bcontext (map_branch_shift b).
  Proof using Type. reflexivity. Qed. *)
End map_branch_shift.

(** Shift a renaming [f] by [k]. *)
Definition shiftn k f :=
  fun n => if Nat.ltb n k then n else k + (f (n - k)).

Notation map_branches_shift ren f :=
  (map (map_branch_shift ren shiftn f)).
  
Fixpoint rename f t : term :=
  match t with
  | tRel i => tRel (f i)
  | tEvar ev args => tEvar ev (List.map (rename f) args)
  | tLambda na T M => tLambda na (rename f T) (rename (shiftn 1 f) M)
  | tApp u v => tApp (rename f u) (map (rename f) v)
  | tProd na A B => tProd na (rename f A) (rename (shiftn 1 f) B)
  | tLetIn na b t b' => tLetIn na (rename f b) (rename f t) (rename (shiftn 1 f) b')
  | tCase ind p c brs =>
    let p' := map_predicate_shift rename shiftn id f p in
    let brs' := map_branches_shift rename f brs in
    tCase ind p' (rename f c) brs'
  | tProj p c => tProj p (rename f c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
    tCoFix mfix' idx
  | x => x
  end. 


(* This function is a version of map where the return type of f is a pair 
and the second argument of the pair is a function f', which 
is used in each recursive call *)


Fixpoint map_pair {A B C : Type} (f : (A -> B) -> C -> (C * (A -> B))) (f' : A -> B) (l : list C) :=
match l with
| [] => ([], f')
| x :: xs => let res := f f' x in 
             let x' := res.1 in
             let f'' := res.2 in
             let res' := map_pair f f'' xs in
             let f_final := res'.2 in
             let xs' := res'.1 in
             (x' :: xs', f_final)
end. 

Section predicate_shift_linearize.

  Context {T : Type}.
  Context (fn : (nat -> T) -> term -> (term*(nat -> T))).
  Context (shift : nat -> (nat -> T) -> nat -> T).
  Context (finst : Instance.t -> Instance.t).
  Context (f : nat -> T).

  Definition map_predicate_shift_linearize (p : predicate term) :=
  let res := map_pair fn f p.(pparams) in
  let params' := res.1 in
  let f' := res.2 in
    {| pparams := p.(pparams); (* we do not want to linearize the parameters *)
        puinst := finst p.(puinst);
        pcontext := p.(pcontext);
        preturn := (fn (shift #|p.(pcontext)| f) p.(preturn)).1 |}. 
(* if we linearize the return type of a case analysis, 
we should use the same renamings in the term so we do not want to use the second projection
of (fn (shift #|p.(pcontext)| f) p.(preturn))
This second projection is only useful to update the list of fresh variables introduced to replace 
second or more occurences of the variables  *)

End predicate_shift_linearize. 

Section map_branch_shift.
  Context {T : Type}.
  Context (fn : (nat -> T) -> term -> term).
  Context (shift : nat -> (nat -> T) -> nat -> T).
  Context (f : nat -> T).

  Definition map_branch_shift_linearize (b : branch term) :=
  {| bcontext := b.(bcontext);
      bbody := fn (shift #|b.(bcontext)| f) b.(bbody) |}.

(*   Lemma map_shift_bbody (b : branch term) :
    fn (shift #|b.(bcontext)| f) (bbody b) = bbody (map_branch_shift b).
  Proof using Type. reflexivity. Qed.
  
  Lemma map_shift_bcontext (b : branch term) :
    (bcontext b) = bcontext (map_branch_shift b).
  Proof using Type. reflexivity. Qed. *)
End map_branch_shift.


Section compute_occurences_predicate. 
 
  
  Context (count_occ : global_declarations -> nat -> term -> nat -> nat).
  Context (fuel : nat).

  Definition compute_occurences_predicate (e : global_declarations) (n : nat) (p : predicate term) :=
    count_occ e n p.(preturn) fuel.

End compute_occurences_predicate.

Section compute_occurences_branch. 

  
  Context (count_occ : global_declarations -> nat -> term -> nat -> nat).
  Context (fuel : nat).

  Definition compute_occurences_branch (e : global_declarations) (n : nat) (b : branch term) :=
    count_occ e (n + #|b.(bcontext)|)  b.(bbody) fuel.

End compute_occurences_branch.

Section compute_occurences_def.

  Context (count_occ : global_declarations -> nat -> term -> nat -> nat). 
  Context (fuel : nat).
  
  Definition compute_occurences_def (e : global_declarations) (n : nat) (d : def term) :=
    count_occ e n (dtype d) fuel + count_occ e n (dbody d) fuel.

End compute_occurences_def. 

(** Finds the number of parameters of an inductive **) 
Fixpoint lookup_npars (l : global_declarations) (kn : kername) :=
match l with
| [] => 0 (* a default value if the inductive is not in the global environment *)
| x :: xs => if eq_kername x.1 kn then match x.2 with
                  | ConstantDecl _ => 0
                  | InductiveDecl ind => ind.(ind_npars)
                end
             else lookup_npars xs kn
end. 

Section compute_occurences.

(** Compute the number of occurrences of the variable n in a term 
if n occurs as a parameter position, then ignore this occurence **) 

  Context (Σ : PCUICProgram.global_env_map).

  Fixpoint compute_occurences_fuel (env: global_declarations) (n: nat) (t : term) (fuel : nat) :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match t with
    | tRel i => if Nat.eqb i n then 1 else 0
    | tVar id => 0
    | tEvar ev l => List.fold_left (fun n' x => n' + compute_occurences_fuel env n x fuel') l 0
    | tSort s => 0
    | tCast t1 ck t2 => compute_occurences_fuel env n t1 fuel' + compute_occurences_fuel env n t2 fuel'
    | tProd na Ty u => compute_occurences_fuel env n Ty fuel' + compute_occurences_fuel env (S n) u fuel'
    | tLambda na Ty u => compute_occurences_fuel env n Ty fuel' + compute_occurences_fuel env (S n) u fuel'
    | tLetIn na b t b' => compute_occurences_fuel env n b fuel' + compute_occurences_fuel env n t fuel' 
      + compute_occurences_fuel env (S n) b' fuel'
    | tCase ind p c brs => compute_occurences_predicate compute_occurences_fuel fuel' env n p  + 
      List.fold_left (fun n' x => n' + compute_occurences_branch compute_occurences_fuel fuel' env n x) brs 0 + compute_occurences_fuel env n c fuel'
    | tApp (tInd ind _) l => let npars := lookup_npars env ind.(inductive_mind) in 
                         let l' := List.skipn npars l in
                         List.fold_left (fun n' x => n' + compute_occurences_fuel env n x fuel') l' 0
    | tApp u l => compute_occurences_fuel env n u fuel' + List.fold_left (fun n' x => n' + compute_occurences_fuel env n x fuel') l 0
    | tProj p c => compute_occurences_fuel env n c fuel'
    | tFix mfix idx =>  List.fold_left (fun n' x => n' + compute_occurences_def compute_occurences_fuel fuel' env (n + List.length mfix) x) mfix 0
    | tCoFix mfix idx => List.fold_left (fun n' x => n' + compute_occurences_def compute_occurences_fuel fuel' env (n + List.length mfix) x) mfix 0
    | tInt _ => 0
    | tFloat _ => 0
    | tConst _ _ => 0
    | tInd _ _ => 0
    | tConstruct _ _ _ => 0
    end
  end.

  Definition compute_occurences (env: global_declarations) (n: nat) (t : term) :=
  let fuel := PCUICSize.size (trans Σ t) in compute_occurences_fuel env n t fuel.

End compute_occurences.

Parameter (Σ : PCUICProgram.global_env_map).

MetaCoq Quote Recursively Definition foo := (forall (n : nat), n + 0 = n).

Print foo.


Compute (compute_occurences Σ ((foo.1).(declarations)) 0 ((tApp
     (tInd
        {|
          inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Coq"%bs], "eq"%bs);
          inductive_ind := 0
        |} [])
     [tInd
        {|
          inductive_mind :=
            (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
          inductive_ind := 0
        |} [];
     tApp (tConst (MPfile ["Nat"%bs; "Init"%bs; "Coq"%bs], "add"%bs) [])
       [tRel 0;
       tConstruct
         {|
           inductive_mind :=
             (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
           inductive_ind := 0
         |} 0 []]; tRel 0]))).
