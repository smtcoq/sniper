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


Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import BinInt.
Require Import Coq.Arith.PeanoNat.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.All.
Require Import List.
Require Import utilities.
Import ListNotations.
Require Import String.


Definition foo := tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
       (tSort
          (Universe.of_levels
             (inr (Level.Level "Sniper.elimination_polymorphism.755"))))
       (tProd {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
          (tRel 0)
          (tProd
             {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
             (tApp
                (tInd
                   {|
                     inductive_mind :=
                       (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                       "list"%string);
                     inductive_ind := 0
                   |} []) [tRel 1])
             (tApp
                (tConst
                   (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                   "not"%string) [])
                [tApp
                   (tInd
                      {|
                        inductive_mind :=
                          (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                          "eq"%string);
                        inductive_ind := 0
                      |} [])
                   [tApp
                      (tInd
                         {|
                           inductive_mind :=
                             (MPfile
                                ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "list"%string);
                           inductive_ind := 0
                         |} []) [tRel 2];
                   tApp
                     (tConstruct
                        {|
                          inductive_mind :=
                            (MPfile
                               ["Datatypes"%string; "Init"%string; "Coq"%string],
                            "list"%string);
                          inductive_ind := 0
                        |} 0 []) [tRel 2];
                   tApp
                     (tConstruct
                        {|
                          inductive_mind :=
                            (MPfile
                               ["Datatypes"%string; "Init"%string; "Coq"%string],
                            "list"%string);
                          inductive_ind := 0
                        |} 1 []) [tRel 2; tRel 1; tRel 0]]]))).

MetaCoq Quote Definition nat_reif := nat.


(* Instantiate a hypothesis with the parameter x *)
Ltac instantiate_par H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => tryif (let H':= fresh H "_" x in assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x)) then idtac else (let H':= fresh H in assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x))
  | _ => fail
      end.


(* Instantiate a hypothesis with the parameter x and return its identifier *)
Ltac instantiate_par_ident H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => let H':= fresh H in 
let _ := match goal with _ => assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x) end in H'
  | _ => fail
      end.


Goal (forall (A : Type) (B : Type), A = A /\ B = B) ->  forall (x : nat) (y : bool), x=x /\ y= y.
intro H.
let H' := instantiate_par_ident H bool in instantiate_par H' bool.
Abort.


Ltac instantiate_tuple_terms H t1 t2 := match t1 with
| (?x, ?t1') => try (let H' := instantiate_par_ident H x in let u := type of H' in
instantiate_tuple_terms H' t2 t2 ) ; try (instantiate_tuple_terms H t1' t2) 
| unit =>  let T := type of H in
           match T with
            | forall (y : ?A), _ => constr_eq A Type ; clear H
            | _ => idtac
            end
end.

Ltac instantiate_tuple_terms_goal H := let t0 := return_tuple_subterms_of_type_type in 
let t := eval cbv in t0 in instantiate_tuple_terms H t t.

Goal (forall (A B C : Type), B = B -> C = C -> A = A) -> nat = nat -> bool = bool.
intros H.
let p := return_tuple_subterms_of_type_type in pose p.
instantiate_tuple_terms_goal H. 
Abort.


Ltac instantiate_tuple_terms_tuple_hyp t terms := match t with 
| (?H, ?t') => instantiate_tuple_terms H terms terms ; instantiate_tuple_terms_tuple_hyp t' terms
| unit => idtac
end.


Ltac instantiate_tuple_terms_tuple_hyp_no_unit t terms := lazymatch t with 
| (?t1, ?t2 ) => instantiate_tuple_terms_tuple_hyp_no_unit t1 terms ; 
instantiate_tuple_terms_tuple_hyp_no_unit t2 terms
| ?H => let T := type of H in 
     match T with 
  | forall (y : ?A), _ => constr_eq A Type ; try (instantiate_tuple_terms H terms terms)
  | _ => try (let U := type of T in constr_eq U Prop ; notHyp H ; let H0 := fresh H in assert (H0 : T) by exact H)
  end
end.

Ltac elimination_polymorphism t0 := 
let t := eval cbv in t0 in 
let terms0 := return_tuple_subterms_of_type_type in 
let terms := eval cbv in terms0 in 
let h0 := hyps in 
let h := eval cbv in h0 in
instantiate_tuple_terms_tuple_hyp_no_unit t terms ; 
instantiate_tuple_terms_tuple_hyp h terms.

Ltac test t0 := 
let t := eval cbv in t0 in 
let h0 := hyps in 
let h := eval cbv in h0 in
let x := constr:((nat, (bool, unit))) in 
instantiate_tuple_terms_tuple_hyp_no_unit t x ; 
instantiate_tuple_terms_tuple_hyp h x.

Ltac test2 t0 :=
let h0 := hyps in
let t := eval cbv in t0 in 
let x := constr:((nat, (bool, unit))) in
instantiate_tuple_terms_tuple_hyp_no_unit t0 x.


Goal (forall (A B C : Type), B = B -> C = C -> A = A) -> nat = nat -> bool = bool.
intro.
elimination_polymorphism (rev_involutive, unit).

Abort.


Tactic Notation "inst" := elimination_polymorphism unit.
Tactic Notation "inst" constr(t) := elimination_polymorphism (t, unit).


Goal (forall (A : Type) (a : A), a = a) -> (forall (x : nat), x = x).
Proof. intros H. inst app_length.

Abort.

Section test.

Variable A : Type. 
 Theorem nil_cons : forall (x:A) (l:list A), [] <> x :: l.
  Proof.
    intros. unfold "<>". intro H. inversion H.
  Qed.

Goal False -> forall (x : nat) (y : bool), x=x /\ y= y.
inst (pair_equal_spec, app_length, nil_cons, app_comm_cons).
Abort.


Goal True -> forall (x:A) (l:list A), [] <> x :: l.
intros.
test2 nil_cons. apply nil_cons0. Qed.

End test.


(** TODO : new tactics **) 

Definition inst_tuple_quote (p : term*(list term)) (strategy : list term -> list term) :=
match p with
| (t, l) => let fix aux t l strategy := match l with
  | [] => []
  | x :: xs => 
    match t with
      | tProd _ Ty u => if is_type Ty then
let tinst := subst10 x u in (tinst, strategy l) :: aux t xs strategy
else [(t, [])]
      | _ => [(t, [])]
    end
  end
in aux t l strategy
end.

Check inst_tuple_quote.

Ltac inst_tuple_list l strategy := 
lazymatch l with 
| [] => constr:(@nil term)
| cons ?p ?l' => match constr:(p) with
    | pair ?x1 ?x2 => lazymatch x2 with 
      | [] =>  constr:([x1])
      | _ =>
    let l0 := eval cbv in (inst_tuple_quote p strategy) in 
    let l1 := inst_tuple_list l0 strategy in 
    let l2 := inst_tuple_list l' strategy in
    let l := eval cbv in (l1 ++ l2) in l
      end
    end
end.

Ltac return_list_terms l :=
 let rec aux l acc :=
lazymatch constr:(l) with
| nil => constr:(acc)
| cons ?x ?xs =>
  let y := metacoq_get_value (tmUnquote x) in 
  let u := constr:(y.(my_projT2)) in 
  let w := eval hnf in u in
  let T := type of w in 
  let b0 := ltac:(is_type_quote_bool T) in 
  let b := eval hnf in b0 in
    lazymatch b with 
    | true => aux xs constr:((x :: acc))
    | false => aux xs acc
    end
end
in aux l (@nil term).

Ltac return_list_subterms_of_type_type := match goal with
|- ?x => let l0 := (get_list_of_closed_subterms x) in let l := eval cbv in l0 in return_list_terms l
end.

Ltac inst_dumb_strat H := 
let H_reif := metacoq_get_value (tmQuote H) in 
let t0 := return_list_subterms_of_type_type in 
let t := eval cbv in t0 in idtac t0 ;
let result0 := (inst_tuple_list constr:([(H_reif, t0)]) (@id (list term))) in
let result := eval cbv in result0 in
pose result.

Goal False.
let u := eval cbv in nat_reif in
let v := eval cbv in foo in 
let x :=
inst_tuple_list [(v, [u])] (@id (list term)) in pose x.
Abort.

Goal forall (A B : Type) (a : A) (b : B), a = a -> b = b.
intros A B.
let foo' := eval unfold foo in foo in
inst_dumb_strat (tmQuote (forall (A : Type) 
         (x : A) (l : list A),
       [] <> x :: l)). let l0 := eval unfold l in l in unquote_list l.
Check nil_cons.
let x := metacoq_get_value (tmQuote (forall (A : Type) 
         (x : A) (l : list A),
       [] <> x :: l)) in pose x.













