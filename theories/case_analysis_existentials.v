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


Require Import utilities. 
Require Import elimination_polymorphism.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import interpretation_algebraic_types. 
Require Import case_analysis.
Unset MetaCoq Strict Unquote Universe Mode.

(** Generates the generation statement in a non-constructive way:
the projection functions are replaced by existentials : 
see the example st_list *)

Fixpoint statement_one_constructor
(n : nat) (* De Brujin index of the list we consider *)
(n' : nat) (* the number of arguments of the constructor *)
(c : term) (* the constructor not applied to its parameters *)
(largs : list term) (* the list of the arguments of the constructor, initialized with the parameters 
and updated with one variable after one recursive call *)
:= match n' with
| 0 => mkEq hole (tRel n) (tApp c largs)
| S n' => tApp <% ex %> [hole ; 
  tLambda (mkNamed "x") hole (statement_one_constructor (S n) n' c ((List.map (lift 1 0) largs)++[tRel 0])) ]
end.

Definition statement_constructors 
(I : term) (* the inductive we want to deal with *)
(typars : list term) (* the type of the parameters *)
(lc : list term) (* the constructors of the inductive (not applied) *)
(largs : list nat) (* for each constructor, the number of their non parametric arguments *) 
:=
let n := Datatypes.length typars in
let lpars := Rel_list n 0 in
let fix aux lpars lc largs :=
match lc, largs with
| [], [] => []
| c :: lc', args :: largs' => statement_one_constructor 0 args c lpars :: aux lpars lc' largs'
| _, _ => [] 
end 
in 
mkProd_rec typars (mkProdName "t" (tApp I lpars) (mkOr_n (aux (List.map (lift 1 0) lpars) lc largs))).

Definition statement_list := statement_constructors <%@list %> [<% Type %>] [<%@nil%> ; <%@cons%>] [0 ; 2].

MetaCoq Unquote Definition st_list := statement_list.

(* Print st_list.
st_list = 
forall (x : Type) (t : list x),
t = [] \/ (exists (x0 : x) (x1 : list x), t = x0 :: x1)
     : Prop *) 

MetaCoq Quote Recursively Definition list_reif_rec := @list.

Fixpoint skipn_forall (n : nat) (t : term) :=
match n with
| 0 => t
| S n' => 
  match t with
  | tProd _ _ u => skipn_forall n' u
  | _ => t
  end
end.

Definition get_nb_args_not_params (t : term) (npars : nat) :=
let t' := skipn_forall npars t in
let fix aux t' n :=
match t' with
| tProd _ _ u => aux u (S n)
| _ => n
end in aux t' 0.

(* generates two lists : the constructors and the number of their arguments *)
Fixpoint find_nb_args_constructors_and_ctors 
(I : inductive) (inst : Instance.t) (npars n : nat) (l : list ((ident × term) × nat))
:=
match l with
| [] => ([], [])
| x :: xs => 
  let resu := find_nb_args_constructors_and_ctors I inst npars (S n) xs in
  let nb := get_nb_args_not_params x.1.2 npars in
  (tConstruct I n inst :: resu.1, nb :: resu.2)
end.

Definition get_indu_and_instance (t : term) :=
match t with
| tInd Ind inst => (Ind, inst)
| _ => ( {|
    inductive_mind :=
      (MPfile ["utilities"; "theories"; "Sniper"],
      "impossible_term");
    inductive_ind := 0
  |}, [])
end.

Definition dest_app (t : term) :=
match t with
| tApp u v => (u, v)
| _ => (t, [])
end.

Ltac prove_by_destruct_varn n  := 
match n with 
| 0 =>
let x := fresh in 
intro x ; destruct x; repeat eexists ; repeat first [ left ; progress (eauto) | first [right | eauto]]
| S ?m => let y := fresh in intro y ; prove_by_destruct_varn m 
end.

Ltac gen_statement_existentials I H :=
let I_reif := metacoq_get_value (tmQuoteRec I) in
let res0 := eval cbv in (dest_app I_reif.2) in
let I_no_app := eval cbv in (res0.1) in
let params := eval cbv in (res0.2) in
let len_params := eval cbv in (Datatypes.length params) in
let indu := eval cbv in (info_inductive I_reif.1 I_no_app ) in
let constructors := eval cbv in (info_nonmutual_inductive I_reif.1 I_no_app).2 in
  match indu with
  | Some ?i => 
    let info_params := eval cbv in (get_params_from_mind i) in 
    let npars := eval cbv in info_params.1 in 
    let typars := eval cbv in info_params.2 in
    let res1 := eval cbv in (get_indu_and_instance I_no_app) in
    let indu := eval cbv in res1.1 in
    let inst := eval cbv in res1.2 in
    let res2 := eval cbv in (find_nb_args_constructors_and_ctors indu inst npars 0 
    (get_na_nb_args_type_list_constructor_body constructors)) in
    let largs := eval cbv in res2.2 in
    let lc := eval cbv in res2.1 in 
    let gen_st_reif := eval cbv in (statement_constructors I_no_app typars lc largs) in
    let gen_st_reif_instances := eval cbv in (subst params 0 (skipn_forall len_params gen_st_reif)) in
    let gen_st := metacoq_get_value (tmUnquoteTyped Prop  gen_st_reif_instances) in
    let nb_vars_intro := eval cbv in (npars-len_params) in 
    assert (H : gen_st) by (prove_by_destruct_varn (nb_vars_intro))
  | None => fail
end.

Section test_gen_statement.

Goal False.
gen_statement_existentials nat H. clear.
gen_statement_existentials list H. clear.
gen_statement_existentials @nelist H. clear.
gen_statement_existentials @biclist H. clear.
gen_statement_existentials Ind_test H. clear.
gen_statement_existentials Ind_test2 H. clear.
gen_statement_existentials (@list nat) H. clear.
Abort.

End test_gen_statement.

(* Checks if a given term is a variable *)
Ltac is_var v :=
let v_reif := metacoq_get_value (tmQuote v) in 
match v_reif with 
| tVar _ => idtac
| _ => fail
end.

(* Returns the tuple of variables in a local context *)
Ltac vars := 
match goal with
| v : _ |- _ => let _ := match goal with _ => is_var v ; revert v end in let acc := vars in 
let _ := match goal with _ => intro v end in constr:((v, acc))
| _ => constr:(unit)
end.

Ltac get_gen_statement_for_variables_in_context :=
let t := vars in 
let rec tac_rec v :=
match v with
| (?v1, ?v') => let T := type of v1 in first [ let U := type of T in constr_eq U Prop ; tac_rec v'  |
                first [let H := fresh in 
                gen_statement_existentials T H; specialize (H v1) ; try (tac_rec v')  | tac_rec v' ]]
| _ => idtac
end in tac_rec t.

Section test_vars_in_context.

Goal forall (A: Type) (x : list nat) (y : nat) (u : list A), 1 = 2 -> False.
Proof. intros ; get_gen_statement_for_variables_in_context. inversion H. Qed.

End test_vars_in_context.

