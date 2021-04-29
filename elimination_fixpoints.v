Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import definitions.
Require Import eta_expand.
Require Import String.
Unset Strict Unquote Universe Mode.

Print term.



Lemma test_length : (forall (H : Type) (H0 : list H),
     #|H0| =
     (fix length (l : list H) : nat :=
        match l with
        | [] => 0
        | _ :: l' => S (length l')
        end) H0) -> (forall (A : Type) (l : list A), #|l| =
     (fun l => match l with
        | [] => 0
        | _ :: l' => S (Datatypes.length l')
        end) l).
Proof. 
intros. simpl. destruct l ; auto. Qed.


Lemma test_length2 : (forall (H : Type) (H0 : list H),
     #|H0| =
     (fix length (l : list H) : nat :=
        match l with
        | [] => 0
        | _ :: l' => S (length l')
        end) H0) -> (forall (A : Type) (l : list A), #|l| =
     (fun l => match l with
        | [] => 0
        | _ :: l' => S (Datatypes.length l')
        end) l).
intros. simpl. match goal with 
| |- context [match ?x with _ => _ end] => destruct x ; auto
end. Qed.


(*  | tFix : mfixpoint term -> nat -> term *)
Print mfixpoint.
(* fun term : Type => list (def term)
     : Type -> Type *)

Print def.

(* Record def (term : Type) : Type := mkdef
  { dname : aname;  dtype : term;  dbody : term;  rarg : nat } 
rarg = index of the recursive argument 
Cet indice est un niveau de db et pas un indice de db *)

MetaCoq Quote Recursively Definition length_reif_rec := Datatypes.length.

Print length_reif_rec.

MetaCoq Quote Definition what_I_want := (forall (A : Type) (l : list A), #|l| =
     (fun l => match l with
        | [] => 0
        | _ :: l' => S (Datatypes.length l')
        end) l).

Print what_I_want.

(* remove the nth last elements of a list *)
Fixpoint rem_last_elem {A} (n : nat) (l : list A) := match l, n with 
| nil, _ => nil
| cons _ _, 0 => l
| cons x xs, S n' => rem_last_elem n' xs
end.

Definition find_args (t1 t2 : term) := 
match t2 with
| tApp _ l => let n:= Datatypes.length l in match t1 with 
        | tApp u l' => (tApp u (rem_last_elem n l'), l)
        | _ => (t1, l)
      end
| _ => (t1, nil)
end.

Fixpoint under_forall_aux (t : term) (l : list (aname*term)) :=
match t with 
| tProd na T u => under_forall_aux u ((na, T)::l)
| _ => (t, l)
end.

Definition under_forall t := under_forall_aux t [].

Fixpoint create_forall (t : term) (l : list (aname*term)) :=
match l with 
| nil => t
| (na, T):: xs => create_forall (tProd na T t) xs
end.

Fixpoint params_eq (t : term) := match t with 
| tApp u l => match l with 
            | [x1; x2; x3] => (u, (x1, x2, x3))
            | _ => (u, (u, u, u))
            end
| _ => (t, (t, t, t))
end.


(* Returns the definition in a fixpoint *)
Fixpoint get_def_in_fix (f: term) := 
match f with 
| tFix l _ => match l with 
          | [] => f
          | x :: xs => x.(dbody)
          end
| _ => f
end.

Definition replace_tFix_by_def (t : term) (def : term) := match t with 
| tFix _ _ => (subst10 def (get_def_in_fix t))
| _ => t
end.


MetaCoq Quote Definition what_I_have := (forall (H : Type) (H0 : list H),
     #|H0| =
     (fix length (l : list H) : nat :=
        match l with
        | [] => 0
        | _ :: l' => S (length l')
        end) H0).

Print what_I_have.

(* (tProd {| binder_name := nNamed "H"%string; binder_relevance := Relevant |}
  (tSort (Universe.of_levels (inr (Level.Level "TransfoCoq.elimination_fixpoints.257"))))
  (tProd {| binder_name := nNamed "H0"%string; binder_relevance := Relevant |}
     (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "list"%string);
           inductive_ind := 0 |} []) [tRel 0])
     (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                             "eq"%string);
           inductive_ind := 0 |} [])
        [tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "nat"%string);
           inductive_ind := 0 |} [];
        tApp
          (tConst
             (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string)
             []) [tRel 1; tRel 0];
        tApp
          (tFix
             [{|
              dname := {|
                       binder_name := nNamed "length"%string;
                       binder_relevance := Relevant |};
              dtype := tProd
                         {|
                         binder_name := nNamed "l"%string;
                         binder_relevance := Relevant |}
                         (tApp
                            (tInd
                               {|
                               inductive_mind := (MPfile
                                                    ["Datatypes"%string; "Init"%string;
                                                    "Coq"%string], "list"%string);
                               inductive_ind := 0 |} []) [tRel 1])
                         (tInd
                            {|
                            inductive_mind := (MPfile
                                                 ["Datatypes"%string; "Init"%string;
                                                 "Coq"%string], "nat"%string);
                            inductive_ind := 0 |} []);
              dbody := tLambda
                         {|
                         binder_name := nNamed "l"%string;
                         binder_relevance := Relevant |}
                         (tApp
                            (tInd
                               {|
                               inductive_mind := (MPfile
                                                    ["Datatypes"%string; "Init"%string;
                                                    "Coq"%string], "list"%string);
                               inductive_ind := 0 |} []) [tRel 2])
                         (tCase
                            ({|
                             inductive_mind := (MPfile
                                                  ["Datatypes"%string; "Init"%string;
                                                  "Coq"%string], "list"%string);
                             inductive_ind := 0 |}, 1, Relevant)
                            (tLambda
                               {|
                               binder_name := nNamed "l"%string;
                               binder_relevance := Relevant |}
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["Datatypes"%string;
                                                          "Init"%string; "Coq"%string],
                                                       "list"%string);
                                     inductive_ind := 0 |} []) [
                                  tRel 3])
                               (tInd
                                  {|
                                  inductive_mind := (MPfile
                                                       ["Datatypes"%string;
                                                       "Init"%string; "Coq"%string],
                                                    "nat"%string);
                                  inductive_ind := 0 |} [])) 
                            (tRel 0)
                            [(0,
                             tConstruct
                               {|
                               inductive_mind := (MPfile
                                                    ["Datatypes"%string; "Init"%string;
                                                    "Coq"%string], "nat"%string);
                               inductive_ind := 0 |} 0 []);
                            (2,
                            tLambda
                              {|
                              binder_name := nNamed "h"%string;
                              binder_relevance := Relevant |} 
                              (tRel 3)
                              (tLambda
                                 {|
                                 binder_name := nNamed "l'"%string;
                                 binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string;
                                                            "Init"%string; "Coq"%string],
                                                         "list"%string);
                                       inductive_ind := 0 |} []) [
                                    tRel 4])
                                 (tApp
                                    (tConstruct
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string;
                                                            "Init"%string; "Coq"%string],
                                                         "nat"%string);
                                       inductive_ind := 0 |} 1 [])
                                    [tApp (tRel 3) [tRel 0]])))]);
              rarg := 0 |}] 0) [tRel 0]])*)


Definition body_reif := tLambda
                         {|
                         binder_name := nNamed "l"%string;
                         binder_relevance := Relevant |}
                         (tApp
                            (tInd
                               {|
                               inductive_mind := (MPfile
                                                    ["Datatypes"%string; "Init"%string;
                                                    "Coq"%string], "list"%string);
                               inductive_ind := 0 |} []) [tRel 2])
                         (tCase
                            ({|
                             inductive_mind := (MPfile
                                                  ["Datatypes"%string; "Init"%string;
                                                  "Coq"%string], "list"%string);
                             inductive_ind := 0 |}, 1, Relevant)
                            (tLambda
                               {|
                               binder_name := nNamed "l"%string;
                               binder_relevance := Relevant |}
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["Datatypes"%string;
                                                          "Init"%string; "Coq"%string],
                                                       "list"%string);
                                     inductive_ind := 0 |} []) [
                                  tRel 3])
                               (tInd
                                  {|
                                  inductive_mind := (MPfile
                                                       ["Datatypes"%string;
                                                       "Init"%string; "Coq"%string],
                                                    "nat"%string);
                                  inductive_ind := 0 |} [])) 
                            (tRel 0)
                            [(0,
                             tConstruct
                               {|
                               inductive_mind := (MPfile
                                                    ["Datatypes"%string; "Init"%string;
                                                    "Coq"%string], "nat"%string);
                               inductive_ind := 0 |} 0 []);
                            (2,
                            tLambda
                              {|
                              binder_name := nNamed "h"%string;
                              binder_relevance := Relevant |} 
                              (tRel 3)
                              (tLambda
                                 {|
                                 binder_name := nNamed "l'"%string;
                                 binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string;
                                                            "Init"%string; "Coq"%string],
                                                         "list"%string);
                                       inductive_ind := 0 |} []) [
                                    tRel 4])
                                 (tApp
                                    (tConstruct
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string;
                                                            "Init"%string; "Coq"%string],
                                                         "nat"%string);
                                       inductive_ind := 0 |} 1 [])
                                    [tApp (tRel 3) [tRel 0]])))]).




MetaCoq Quote Definition length_reif := Datatypes.length.

Definition toto := (tProd {| binder_name := nNamed "H"%string; binder_relevance := Relevant |}
  (tSort (Universe.of_levels (inr (Level.Level "TransfoCoq.elimination_fixpoints.257"))))
  (tProd {| binder_name := nNamed "H0"%string; binder_relevance := Relevant |}
     (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "list"%string);
           inductive_ind := 0 |} []) [tRel 0])
     (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                             "eq"%string);
           inductive_ind := 0 |} [])
        [tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "nat"%string);
           inductive_ind := 0 |} [];
 tApp
          (tConst
             (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string)
             []) [tRel 1; tRel 0]; tApp (subst10 (tApp
          (tConst
             (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string)
             []) [tRel 1]) body_reif) [tRel 0]]))).



MetaCoq Unquote Definition toto_unquote := toto.
Print toto_unquote.


Print length_reif_rec.



Definition get_args (t : term) := match t with 
| tApp u l => l
| _ => nil
end.

Definition new_app (t : term) (l : list term) := match t with 
| tApp u _ => tApp u l
| _ => t
end.


Ltac eliminate_fix_hyp H := 
let T := type of H in
let H' := fresh in quote_term T ltac:(fun T =>
let p := eval cbv in (under_forall T) in 
let eq := eval cbv in p.1 in
let list_quantif := eval cbv in p.2 in
let get_info_eq := eval cbv in (params_eq eq) in 
let eq_reif := eval cbv in get_info_eq.1 in 
let A := eval cbv in get_info_eq.2.1 in 
let t := eval cbv in get_info_eq.2.2.1 in 
let u := eval cbc in get_info_eq.2.2.2 in
let prod := eval cbv in (find_args t u) in 
let args := eval cbv in prod.2 in (* the arguments of u *)
let def := eval cbv in prod.1 in 
let u_no_fix := eval cbv in (replace_tFix_by_def u def) in 
idtac).









let l := eval cbv in (get_args T) in 
let l' := eval cbv in (replace_tFix_by_def l t) in 
let eq := eval cbv in (new_app T l')
in idtac eq ;
run_template_program (tmUnquote eq) 
ltac:(fun z => 
let w := eval hnf in (z.(my_projT2)) 
in pose w))))
| _ => fail "not an equality" 
end.

Goal Nat.add = (fun n m : nat => match n with
                            | 0 => m
                            | S p => S (p + m)
                            end).
Proof.
unfold Nat.add.
Abort.

Goal False.
get_def @Datatypes.length.
get_def Nat.add.
eliminate_fix_hyp add_def.
assert P.
unfold P. 
Fail eliminate_fix_hyp length_def.

 expand_hyp length_def.
Abort.














