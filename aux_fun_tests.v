Add Rec LoadPath "/home/pierre/depots/sniper" as Sniper.
(* \Q why is this line needed? *)
 
Require Import utilities. 
Require Import interpretation_algebraic_types.
Require Import elimination_polymorphism.
Require Import eliminators.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.

(* function to comment :  pose_inductive_tac *)

Open Scope string_scope.  

Import ListNotations MonadNotation. 



Definition get_ind_ident (kerna : kername) := let (mdp , idind) := kerna in idind.


Locate pose_inductive_tac.

MetaCoq Quote Definition Type_reif := Eval hnf in Type.
MetaCoq Quote Definition Prop_reif := Eval hnf in Prop.
MetaCoq Quote Definition Set_reif := Eval hnf in Set.
MetaCoq Quote Definition eq_reif := Eval hnf in @eq. 

MetaCoq Quote Definition nat_reif := nat.
MetaCoq Quote Recursively Definition nat_env_reif := nat.


Definition list_nat := @list nat.
MetaCoq Quote Definition list_nat_reif :=  (@list nat).
MetaCoq Quote Recursively Definition list_nat_env_reif := list_nat.             
MetaCoq Quote Definition cons_nat_type_reif := (nat -> list_nat -> list_nat).
MetaCoq Quote Definition nil_type_reif := (forall (A : Type), list A).
(* \Q nil_type_reif and cons_nat_reif do not work because do not
currently have  the right universes levels *)


MetaCoq Quote Definition cons_reif := cons.

MetaCoq Quote Definition zero_reif := 0.
MetaCoq Quote Definition one_reif := 1.
MetaCoq Quote Definition two_reif := 2.


MetaCoq Quote Definition nil_nat_reif := Eval cbn in (@nil nat).
MetaCoq Quote Definition list_one_two_reif := Eval cbn in [1 ; 2].
MetaCoq Quote Definition list_one_two_two_reif := Eval cbn in [1 ; 2 ; 2].

MetaCoq Quote Definition list_one_two_two_reif' := (List.app [1] [2 ; 2]).



(** Reified objects functions *)
 
Definition cons_nat := @cons nat.



MetaCoq Quote Definition length_reif := @List.length.
MetaCoq Quote Definition le_reif := le.
MetaCoq Quote Definition S_reif := Eval cbn in S.
MetaCoq Quote Recursively Definition S_env_reif := S.
Print S_env_reif.
Print S_reif. 
MetaCoq Quote Definition O_reif := O.
MetaCoq Quote Definition add_reif := Eval cbn in Nat.add.
MetaCoq Quote Definition nil_reif := nil.
MetaCoq Quote Recursively Definition nil_env_reif := nil.
MetaCoq Quote Recursively Definition cons_env_reif := cons.
MetaCoq Quote Recursively Definition cons_nat_env_reif := cons_nat.
MetaCoq Quote Definition cons_nat_reif := cons_nat.
MetaCoq Quote Definition list_reif := @list.
MetaCoq Quote Recursively Definition list_env_reif := @list.

Print list_env_reif.

Definition nat_indu := ltac:(let s := fresh in  pose_inductive_tac nat s ; exact s).
Definition list_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).
Definition list_nat_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).






Definition nat_oind := {|
ind_name := "nat"%string;
ind_type := tSort (Universe.of_levels (inr Level.lSet));
ind_kelim := IntoAny;
ind_ctors := [("O"%string, tRel 0, 0);
             ("S"%string,
             tProd
               {|
               binder_name := nAnon;
               binder_relevance := Relevant |}
               (tRel 0) (tRel 1), 1)];
ind_projs := [];
ind_relevance := Relevant |}.



Ltac pose_oind_tac t i idn := let s := fresh "s" in pose_mind_tac t s ; pose (nth i s.(ind_bodies)  nat_oind) as idn; simpl in idn ; clear s.
(* pose_oind take an (unreified) inductive  I and outputs the i-th one_inductive_block of I *) 
(* when I is not a mutual inductive, i should be equal to 0 *)
(* the tactic uses nat_oind as the defaut value for nth *)

Definition list_oind := ltac:(let s := fresh in pose_oind_tac list 0 s ; compute in s ; exact s).
Print list_oind.

 

(* 
Inductive my_type :=
  | A : my_type
  | B : my_type -> my_type
  | C : my_type -> my_type.

MetaCoq Quote Definition mt_reif := my_type.  
MetaCoq Quote Definition A_reif := A. 
MetaCoq Quote Definition B_reif := B.
MetaCoq Quote Definition C_reif := C.
*)


(**** eliminators.v ****)

Goal False.

Print nil_type_reif.
pose (tProd
  (mkNamed "A")
  (tSort
     (Universe.of_levels
        (inr
           (Level.Level
              "Sniper.aux_fun_tests.465"))))
  (tApp
    list_reif [tRel 0]))
as blut0.
pose (tProd
  (mkNamed "A")
  (tSort
     (Universe.of_levels
        (inr
           (Level.Level
              "Sniper.aux_fun_tests.387"))))
  (tProd
     {|
       binder_name := nAnon;
       binder_relevance := Relevant
     |} (tRel 0)
     (tProd
        {|
          binder_name := nAnon;
          binder_relevance := Relevant
        |}
        (tApp
           list_reif [tRel 1])
        (tApp list_reif [tRel 2])))) as blut1.
let list_info := fresh "list_info" in get_info_quote list list_info. 
pose list_info.2 as list_indu. compute in list_indu. (* \Q pq ça ne calcule pas ? *)
pose list_info.1.2 as list_I_app. compute in list_I_app.
pose list_info.1.1.2 as list_lpars. compute in list_lpars.
pose list_info.1.1.1.2 as list_total_args. compute in list_total_args.
pose list_info.1.1.1.1.2 as list_list_args. compute in list_list_args.
pose list_info.1.1.1.1.1.2 as list_list_ty. compute in list_list_ty.
pose list_info.1.1.1.1.1.1.2 as list_ty_pars. compute in list_ty_pars.
pose list_info.1.1.1.1.1.1.1 as list_npars.  hnf in list_npars. 
(* Print list_I_app. *) (* gives the parameter i *)
get_list_args_len_quote list list_lal.
get_ty_arg_constr list list_tarc.

pose ((tApp (* en mettant un idtac dans eliminators.v *)
   (tInd
      {|
        inductive_mind :=
          (MPfile
             ["Datatypes"; "Init";
             "Coq"], "list");
        inductive_ind := 0
      |} []) [tRel 0])) as list_ty_default.
(* on aussi tRel 0 qui doit correspondent à un autre ty_default *)

(* pour ty_default avec un idtac *)



pose (tLambda
   {|
     binder_name := nNamed "x";
     binder_relevance := Relevant
   |}
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 2])
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 3])) as rtyp1. 
pose 
(tLambda
   {|
     binder_name := nNamed "x";
     binder_relevance := Relevant
   |}
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 2]) 
   (tRel 3)) as rtyp0.


(* proj_one_constructor_default_var (i : term) (ty_default : term)
 (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) *) 
clear list_info.
let x := constr:(proj_one_constructor_default_var  (tApp list_reif [tRel 0]) 
 (tApp list_reif [tRel 0])  
list_indu 1 0 1 list_tarc rtyp1)
in pose x as y; compute in y.
Print tCase.
pose_unquote_term_hnf y projtruc.
Abort.
