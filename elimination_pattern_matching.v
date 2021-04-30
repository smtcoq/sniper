Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import definitions.
Require Import eta_expand.
Require Import List.


Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).

MetaCoq Quote Definition unit_reif := unit.

MetaCoq Quote Definition eq_reif := Eval cbn in @eq.


(* Equality of type B between two terms *)
Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].


(* find the bodies of an inductive simply quoted *)
Fixpoint get_decl_inductive (I : term) (e : global_env) :=
match I with 
| tInd ind _ => match ind.(inductive_mind) with
          | (file, ident) => match e with 
                      | [] => None 
                      | (na,d) :: e' => 
                                (match d with
                                  | InductiveDecl mind => if (String.eqb
ident na.2) then let loind := ind_bodies mind in Some loind else get_decl_inductive I e'
                                  | _ => get_decl_inductive I e'
                               end)    
    end
end
| _ => None
end.

(* find the number of parameters of an inductive simply quoted *)
Fixpoint get_npar_inductive (I : term) (e : global_env) :=
match I with 
| tInd ind _ => match ind.(inductive_mind) with
          | (file, ident) => match e with 
                      | [] => 0
                      | (na,d) :: e' => 
                                (match d with
                                  | InductiveDecl mind => if (String.eqb
ident na.2) then ind_npars mind else get_npar_inductive I e'
                                  | _ => get_npar_inductive I e'
                               end)    
    end
end
| _ => 0
end.



Definition get_type_constructor (c : term):=
match c with
| tConstruct ind _ _ => let kn := ind.(inductive_mind) in 
tInd {| inductive_mind := kn ; inductive_ind := 0 |} []
| _ => unit_reif
end.



(* does not work for mutual inductives *)
Ltac list_ctors_and_types I :=
run_template_program (tmQuoteRec I) ltac:(fun t => 
let x := eval compute in (get_decl_inductive t.2 t.1) in match x with
| Some (?y::_) => let z := eval compute in y.(ind_ctors) in pose z
| None => fail
end).

(*  in the type of the constructor we need to susbtitute the free variables by the corresponding inductive type *)

Fixpoint subst_type_constructor_list' (l : list ((string × term) × nat)) (p : term) :=

match l with 
| nil => nil
| ((_, Ty), _):: l' => (subst10 p Ty)  :: (subst_type_constructor_list' l' p)
end.



MetaCoq Quote Recursively Definition list_reif := list.
Print list_reif.


(* Fixpoint subst_type_constructor_list_no_param (l : list ((string × term) × nat)) (T : term) (n : nat) :=
let l' := subst_type_constructor_list' l T n in 
let fix aux (l' : list term) n := match (n, l') with
| (0, _) => l'
| (S m, nil) => nil
| (S m, x :: xs) => aux xs m
end in rev (aux  (rev l') n).
Check subst_type_constructor_list_no_param. *)

Definition type_no_app t := match t with
| tApp u l => (u, l)
| _ => (t, [])
end.

(* Ltac list_types_of_ctors I :=
run_template_program (tmQuoteRec I) ltac:(fun t => 
let x := eval compute in (get_decl_inductive t.2 t.1) in match x with
| Some (?y::_) => let z := eval cbv in y.(ind_ctors) in 
let v := eval cbv in t.2 in let u := eval cbv in (subst_type_constructor_list' z v) in
pose u
| None => fail 1
end). *)

(* beta reduction *)
Fixpoint typing_prod_list (T : term) (args : list term) := 
match T with
| tProd _ A U => match args with 
        | nil => T
        | x :: xs => typing_prod_list (subst10 x U) xs
        end
| _ => T
end.


Fixpoint subst_type_constructor_list (l : list ((string × term) × nat)) (p : term × (list term)) (n : nat) :=
let T := p.1 in 
let args := p.2 in
match l with 
| nil => nil
| ((_, Ty), _):: l' => (typing_prod_list (subst10 T Ty) args) :: (subst_type_constructor_list l' p n)
end.

(* t is a term recursively quoted *)
Definition list_types_of_each_constructor t :=
let v := (type_no_app t.2) in (* the inductive not applied to its parameters and the list of its parameters *)
let x := get_decl_inductive v.1 t.1 in (* the first inductive declaration in a mutual inductive block  *)
let n := get_npar_inductive v.1 t.1 in  (* numbers of parameters *)
match x with
| Some y => match y with 
          | nil => nil
          | cons y' _ => let z := y'.(ind_ctors) in let u := 
subst_type_constructor_list z v n in u 
          end
| None => nil
end.



Ltac unquote_list l :=
match constr:(l) with
| nil => idtac
| cons ?x ?xs => unquote_term x ; unquote_list xs
end.






Fixpoint get_info_inductive (I : term) := 
let p := type_no_app I in match p.1 with
| tInd ind inst => Some ((ind, inst), p.2)
| _ => None
end.


Fixpoint get_list_of_rel (i : nat) := match i with
| 0 => []
| S n => (get_list_of_rel n) ++ [tRel n] (* n *)
end.




(* gets the list of constructors given an inductive recursively quoted and the number of its constructors *)
Definition get_list_ctors_tConstruct I n := 
let I' := get_info_inductive I in match I' with
| Some J => let ind := J.1.1 in let inst := J.1.2 in let args := J.2 in let 
fix aux n' ind' inst' args :=
match n' with 
| 0 => []
| S m =>  (aux m ind' inst' args) ++ [tApp (tConstruct ind' m inst') args]
end
in aux n J.1.1 J.1.2 J.2
| None => []
end.

(* Definition list_types_of_each_constructor_no_param  t :=
let x := get_decl_inductive t.2 t.1 in let n:= get_npar_inductive t.2 t.1 in 
match x with
| Some y => match y with 
          | nil => nil
          | cons y' l => let z := y'.(ind_ctors) in let v := t.2 in let u := 
subst_type_constructor_list_no_param z v n in u
          end
| None => nil
end. *)

Ltac list_ctors_unquote_requote_rec t :=
run_template_program (tmUnquote t) (fun t => 
let x:= eval hnf in t.(my_projT2) in run_template_program (tmQuoteRec x) ltac:(fun t => 
let x:= eval cbv in (list_types_of_each_constructor t) in pose x)).



Definition get_type_of_args t := 
let fix aux t (acc : list term) := match t with 
| tLambda _ ty s => aux s (ty::acc)
| tProd _ ty s => aux s (ty :: acc)
| _ => acc 
end in aux t [].



Ltac prove_hypothesis H :=
repeat match goal with
  | H' := ?x : ?P |- _ =>  lazymatch P with 
                | Prop => let def := fresh in assert (def : x) by 
(intros; rewrite H; auto) ;  clear H'
          end
end.





Definition get_env (T: term) (n  : nat) := 
let fix aux T n acc := 
match (T, n) with
| (tProd _ A t, 0) => ((acc, t), A)
| (tProd _ A t, S n') => aux t n' (A::acc)
| _ => ((acc, T), T)
end
in aux T n [].




Fixpoint prenex_quantif_list (l : list term) (t : term):= 
match l with
| [] => t 
| x :: xs => prenex_quantif_list xs (mkProd x t)
end.

Fixpoint remove_elem (n : nat) (l : list term) := match l, n with
| [], _ => []
| _, 0 => l
| x :: xs, S m => remove_elem m xs
end.


Definition list_of_args (t : term) := let fix aux acc t := match t with
| tProd _ t1 t2 => aux (t1 :: acc) t2
(* | tApp t l => let n := Datatypes.length l in remove_elem n 
(rev (aux acc t)) (* we need to remove the n first elements applied in order to avoid quantifying over them *) *)
| _ => acc
end in aux [] t.


Definition E := (tApp
       (tInd
          {|
          inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                            "eq"%string);
          inductive_ind := 0 |} [])
       [tRel 2;
       tApp (tConst (MPfile ["List"%string; "Lists"%string; "Coq"%string], "hd"%string) [])
         [tRel 2; tRel 1; tRel 0];
       tCase
         ({|
          inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                            "list"%string);
          inductive_ind := 0 |}, 1, Relevant)
         (tLambda {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
            (tApp
               (tInd
                  {|
                  inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                    "list"%string);
                  inductive_ind := 0 |} []) [tRel 2]) (tRel 3)) (tRel 0)
         [(0, tRel 1);
         (2,
         tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |} 
           (tRel 2)
           (tLambda {| binder_name := nNamed "l0"%string; binder_relevance := Relevant |}
              (tApp
                 (tInd
                    {|
                    inductive_mind := (MPfile
                                         ["Datatypes"%string; "Init"%string; "Coq"%string],
                                      "list"%string);
                    inductive_ind := 0 |} []) [tRel 3]) (tRel 1)))]]).
Definition l_constructor := [tApp
        (tConstruct
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "list"%string);
           inductive_ind := 0 |} 0 []) [tRel 2];
     tApp
       (tConstruct
          {|
          inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                            "list"%string);
          inductive_ind := 0 |} 1 []) [tRel 2]].
Definition l_ty_constructor := [tApp
         (tInd
            {|
            inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                              "list"%string);
            inductive_ind := 0 |} []) [tRel 2];
      tProd {| binder_name := nAnon; binder_relevance := Relevant |} 
        (tRel 2)
        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
           (tApp
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "list"%string);
                 inductive_ind := 0 |} []) [tRel 3])
           (tApp
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "list"%string);
                 inductive_ind := 0 |} []) [tRel 4]))].

Eval cbv in list_of_args (hd unit_reif ( l_ty_constructor)).

Definition l := [tRel 0;
      tSort
        {|
        Universe.t_set := {|
                          UnivExprSet.this := [(Level.Level "Coq.Lists.List.1", 0)];
                          UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                 (Level.Level "Coq.Lists.List.1", 0) |};
        Universe.t_ne := Logic.eq_refl |}].


Definition prenex_quantif_list_ctor (c : term) (l : list term) (l' : list term) (E : term) :=
(* c is the constructor reified, l is the list of the type of its arguments, l' is the list of the 
type of the prenex quantification in the hypothesis, E is the environment *)
let n := Datatypes.length l in
prenex_quantif_list l' (prenex_quantif_list l (subst [tApp (lift n 0 c) (rev (get_list_of_rel n))] 0 (lift n 1 E))).

Definition get_equalities (E : term) (l_ctors : list term) (l_ty_ctors  : list term) (l_ty : list term) :=
let fix aux (E : term) (l_ctors : list term) (l_ty_ctors  : list term) (l_ty : list term) acc :=
match (l_ctors, l_ty_ctors) with
| (nil, _) | (_ , nil) => acc
| (x :: xs, y :: ys) => aux E xs ys l_ty
((prenex_quantif_list_ctor x (list_of_args y) l_ty E) :: acc)
end
in aux E l_ctors l_ty_ctors l_ty [].

(*TODO : tactique qui prend la liste en paramètre + l'hypothèse H et qui prouve l'unquote de la liste 
grâce à H *)

Ltac prove_list_hypothesis H l := match constr:(l) with 
| [] => idtac 
| cons ?x ?xs => run_template_program (tmUnquote x) (fun x => let y := eval cbv in x.(my_projT2) in 
assert y by (rewrite H ; reflexivity) ; prove_list_hypothesis H constr:(xs))
end.

Ltac count_prenex_forall H :=
  match H with
| forall _ : _, ?A => constr:(S ltac:(count_prenex_forall A))
| _ => constr:(0)
end.


Ltac eliminate_pattern_matching H :=

  let n := fresh "n" in 
  epose (n := ?[n_evar] : nat);
  let T := type of H in
  let H' := fresh in
  assert (H' : False -> T);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x :=
        match goal with
      | |- context C[match x with _ => _ end] =>  match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n_evar := p) 
                                        end
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail
    end 
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ;
run_template_program (tmQuoteRec T) (fun Env => 
let T := eval cbv in Env.2 in
let e := eval cbv in Env.1 in
let prod := eval cbv in (get_env T n) in clear n ;
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in
let l_ty_ctors := eval cbv in (list_types_of_each_constructor (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct A n) in
let list_of_hyp := eval cbv in (get_equalities E l_ctors l_ty_ctors l) in
 unquote_list list_of_hyp ; prove_hypothesis H )] ; clear H.


MetaCoq Quote Recursively Definition foo_reif := (fun A (l: list A) => match l with 
| [] => unit
| cons x xs => unit
end).


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


Goal ((forall (A: Type) (x : A) (l : list A) (n : nat), hd x l = match l with 
| [] => x 
| y :: ys => y
end) -> True).
Proof.
intros H. 
eliminate_pattern_matching H.
expand_fun min1.
expand_fun hd.
eliminate_pattern_matching H2.
eliminate_pattern_matching H.

Abort.

Goal ((forall (A: Type) (x : A) (a : A) (l : list A), 
@hd A x (@cons A a l) = match (@cons A a l) with
| nil => x
| y :: xs => y
end)).
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_pattern_matching H')). assumption.
Qed.


Goal ((forall (A: Type) (l : list A), 
@List.length A l = match l with
| nil => 0
| y :: xs => length xs + 1
end) -> True).
intro H.
eliminate_pattern_matching H.
exact I. 
Qed.


Goal ((forall (H : Type) (H0 : list H),
     #|H0| =
     (fix length (l : list H) : nat :=
        match l with
        | [] => 0
        | _ :: l' => S (length l')
        end) H0) -> True).
intro H.
Fail eliminate_pattern_matching H.
Abort.



















