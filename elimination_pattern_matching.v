(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyfalse (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import SMTCoq.SMTCoq.

Require Import MetaCoq.Template.All.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import String.
Require Import utilities.
Require Import definitions.
Require Import elimination_fixpoints.
Require Import expand.
Require Import List.


Fixpoint codomain (t : term) := match t with 
| tProd _ _ u => codomain u 
| _ => t 
end.




(* Build the list of constructors and their types applied to the parameters *)
Definition build_ctor_ty_ctor_applied_to_parameters (args_in_statement : list term) (p : term * term) := let ctor := p.1 in let ty_ctor := p.2 in 
let ty_args := (no_app (codomain ty_ctor)).2
in let fix aux args_in_statement ty_args ctor ty_ctor := match args_in_statement, ty_args with
| nil, _ => (ctor, ty_ctor)
| _, nil => (ctor, ty_ctor)
| x_in_statement :: args_in_statement', x_in_ty :: ty_args' =>  match x_in_ty with 
        | tRel k => aux args_in_statement' ty_args' (tApp ctor [x_in_statement]) (tApp ty_ctor [x_in_statement])
        | _ => aux args_in_statement' ty_args' ctor ty_ctor
        end 
end
in aux args_in_statement ty_args ctor ty_ctor.
        



Definition get_info_inductive (I : term) := 
let p := no_app I in match p.1 with
| tInd ind inst => Some (ind, inst)
| _ => None
end.

Definition get_info_inductive_args (I : term) := 
let p := no_app I in match p.1 with
| tInd ind inst => Some ((ind, inst), p.2)
| _ => None
end.

Fixpoint get_list_of_rel (i : nat) := match i with
| 0 => []
| S n => ((get_list_of_rel n) ++ [tRel n])%list (* n *)
end.


(* gets the list of constructors applied to their parameters
 given an inductive recursively quoted and the number of its constructors *)
Definition get_list_ctors_tConstruct_applied I n := 
let I' := get_info_inductive_args I in match I' with
| Some J => let ind := J.1.1 in let inst := J.1.2 in let args := J.2 in let
fix aux n' ind' inst' args :=
match n' with 
| 0 => []
| S m =>  (aux m ind' inst' args) ++ [tApp (tConstruct ind' m inst') args]
end
in aux n J.1.1 J.1.2 J.2
| None => []
end.

(* gets the list of constructors given an inductive recursively quoted and the number of its constructors *)
Definition get_list_ctors_tConstruct I n := 
let I' := get_info_inductive I in match I' with
| Some J => let ind := J.1 in let inst := J.2 in let 
fix aux n' ind' inst' :=
match n' with 
| 0 => []
| S m =>  ((aux m ind' inst') ++ [tConstruct ind' m inst'])%list
end
in aux n J.1 J.2
| None => []
end.


Definition get_type_of_args t := 
let fix aux t (acc : list term) := match t with 
| tLambda _ ty s => aux s (ty::acc)
| tProd _ ty s => aux s (ty :: acc)
| _ => acc 
end in aux t [].



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




Definition prenex_quantif_list_ctor (c : term) (l : list term) (l' : list term) (E : term) :=
(* c is the constructor reified, l is the list of the type of its arguments, l' is the list of the 
type of the prenex quantification in the hypothesis, E is the environment *)
let n := Datatypes.length l in
prenex_quantif_list l' (prenex_quantif_list l (subst [tApp (lift n 0 c) (rev (get_list_of_rel n))] 0 (lift n 1 E))).

Definition get_equalities (E : term) (l_ctors_and_ty_ctors : list (term * term))  (l_ty : list term) := 

let fix aux (E : term) l_ctors_and_ty_ctors (l_ty : list term) acc :=
match l_ctors_and_ty_ctors  with
| nil => acc
| (x, y):: xs => aux E xs l_ty
((prenex_quantif_list_ctor x (list_of_args y) l_ty E) :: acc)
end
in aux E l_ctors_and_ty_ctors l_ty [].



Ltac eliminate_pattern_matching H k :=
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
let l_ctors := eval cbv in (get_list_ctors_tConstruct_applied A n) in 
let l_ctor_and_ty_ctor := eval cbv in (combine l_ctors l_ty_ctors) in
let list_of_hyp := eval cbv in (get_equalities E l_ctor_and_ty_ctor l) in
let st_quoted := eval cbv in (nth k (rev list_of_hyp) unit_reif) in
let st0 := metacoq_get_value (tmUnquote st_quoted) in 
let st := eval hnf in (my_projT2 st0) in assert st by (intros; apply H))] ; clear H.

Ltac eliminate_pattern_matching_cont H k cont :=
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
let l_ctors := eval cbv in (get_list_ctors_tConstruct_applied A n) in 
let l_ctor_and_ty_ctor := eval cbv in (combine l_ctors l_ty_ctors) in
let list_of_hyp := eval cbv in (get_equalities E l_ctor_and_ty_ctor l) in
let st_quoted := eval cbv in (nth k (rev list_of_hyp) unit_reif) in
let st0 := metacoq_get_value (tmUnquote st_quoted) in 
let st := eval hnf in (my_projT2 st0) in let name := fresh in 
assert (name : st) by (intros; apply H) ; cont name)] ; clear H.

Ltac create_evars_for_each_constructor i := 
let y := metacoq_get_value (tmQuoteRec i) in 
let n:= eval cbv in (get_nb_constructors y.2 y.1) in
let rec tac_rec u := match constr:(u) with 
      | 0 => idtac
      | S ?m => let H' := fresh in let H'_evar := fresh H' in epose (H' := ?[H'_evar] : Prop) ; tac_rec m
end in tac_rec n.

Ltac create_evars_for_each_constructor_test i := 
let y := metacoq_get_value (tmQuoteRec i) in 
let n:= eval cbv in (get_nb_constructors y.2 y.1) in
let rec tac_rec u := match constr:(u) with 
      | 0 => idtac
      | S ?m => let H' := fresh in let H'_evar := fresh H' in epose (H' := ?[H'_evar] : Prop) ; tac_rec m
end in tac_rec n.

Goal True.
create_evars_for_each_constructor bool.
create_evars_for_each_constructor unit.
create_evars_for_each_constructor nat.
create_evars_for_each_constructor_test nat.
Abort.



Ltac create_evars_and_inst_rec n l := 
match constr:(n) with 
| 0 => l
| S ?m => let H := fresh in 
let H_evar := fresh in 
let _ := match goal with _ => epose (H := ?[H_evar] : nat) end in 
create_evars_and_inst_rec m constr:(H :: l) end.

Ltac intro_and_return_last_ident n := 
match constr:(n) with
| 0 => let u := fresh in let _ := match goal with _ => intro u end in u
| S ?m => let H := fresh in let _ := match goal with _ => intro H end in intro_and_return_last_ident m
end.


Ltac intro_and_tuple_rec n l := 
match constr:(n) with
| 0 => let u := fresh in let _ := match goal with _ => intro u end in constr:((u, l))
| S ?m => let H := fresh in let _ := match goal with _ => intro H end in intro_and_tuple_rec m (H, l)
end.

Ltac intro_and_tuple n :=
intro_and_tuple_rec n unit.

Ltac intro_and_tuple' n :=
match constr:(n) with
| 0 => let u := fresh in let _ := match goal with _ => intro u end in constr:((u, unit))
| S ?m => let H := fresh in let _ := match goal with _ => intro H end in let l:= intro_and_tuple' m in
constr:((H, l))

end.


Lemma test_intro_and_tuple :  forall (A B : Type) (C : A) (n n' : nat) (x : bool), x = x.
let p := intro_and_tuple 4 in pose (p0 := p). clear p0. revert H H0 H1 H2 H3.
let p := intro_and_tuple' 4 in pose p.
reflexivity. Qed.


Ltac create_evars_and_inst n := 
create_evars_and_inst_rec n (@nil nat).



Ltac revert_tuple p := 
lazymatch constr:(p) with
| (?x, ?y) => revert_tuple y ; revert_tuple x 
| _ => try (revert p)
end.

Ltac revert_tuple_clear p indu :=
lazymatch constr:(p) with
| (?x, ?y) => match indu with 
          | context [x] => clear x
          | _ => revert x
           end 
; revert_tuple_clear y indu
| unit => idtac
end.

Definition head_tuple (A B : Type) (x : A×B) := match x with
|(y, z) => y
end.

Definition tail_tuple (A B : Type) (x : A*B) := match x with
|(y, z) => z
end.


Lemma test_revert_tuple : forall (A B : Type) (C : A) (n n' : nat) (x : bool), x = x.
intros. revert_tuple (A, B, C, n, n', x, unit). reflexivity. Qed. (*  unit in first *)

Ltac detect_var_match H :=

let T := type of H in 
let H' := fresh in 
assert (H' : False -> T) by
(match goal with | |-context C[match ?x with _ => _ end] => idtac end; let Hfalse := fresh in 
intro Hfalse; destruct Hfalse) ; clear H' ; idtac.


Ltac remove_app t :=
lazymatch constr:(t) with 
| ?u ?v => remove_app u 
| _ => t
end.

Goal forall (A : Type) (x: list A), x = x.
Proof. intros. let T := type of x in let T' := remove_app T in pose T'.
reflexivity.
Qed.


Ltac revert_count := 
let rec revert_count_rec n :=
match goal with
| H : _ |- _ => let _ := match goal with _ => revert H end in revert_count_rec (S n)
| _ => n
end in revert_count_rec 0.


Ltac hyps := 
match goal with
| H : _ |- _ => let _ := match goal with _ => revert H end in let acc := hyps in 
let _ := match goal with _ => intro H end in constr:((H, acc))
| _ => constr:(unit)
end.

Ltac clear_if_in_term p t := 
match p with 
| (?x, ?y) => match t with 
              | context [x] => try (clear x) 
              | _ => idtac end ; clear_if_in_term y t 
| unit => idtac
end.

Ltac eliminate_dependent_pattern_matching H :=
  let n := fresh "n" in 
  let T := fresh "T" in 
  epose (n := ?[n_evar] : nat) ;
  epose (T := ?[T_evar]) ;
  let U := type of H in
  let H' := fresh in
  assert (H' : False -> U);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x :=
        match goal with
      | |- context C[match x with _ => _ end] => match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n_evar := p) ; 
                                              let Ty := type of x in let T' := remove_app Ty in
                                              instantiate (T_evar := T') 
                                     end 
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail 
      end
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ; let indu := eval unfold T in T in 
create_evars_for_each_constructor indu ; let foo := fresh in assert 
(foo : False -> U) by 
(let Hfalse' := fresh in intro Hfalse' ; 
let nb_var := eval unfold n in n in
let t := intro_and_tuple nb_var in 
let var_match := eval cbv in (head_tuple _ _ t) in 
let var_to_revert := eval cbv in (tail_tuple _ _ t) in 
case var_match ; 
let indu' := type of var_match in clear var_match ; 
revert_tuple_clear var_to_revert indu' ;
match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse' end)
; clear foo ; 
repeat match goal with 
| u : Prop |-_ => let H0 := fresh in let u' := eval unfold u in u in assert (H0 : u') by 
( intros; try (rewrite H); reflexivity); clear u ; try (eliminate_dependent_pattern_matching H0)end] ; clear H ; 
clear n; clear T.


Module Tests.


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
expand_fun min1.
expand_fun hd.
eliminate_pattern_matching H1 0.

Abort.

Goal ((forall (A: Type) (x : A) (a : A) (l : list A), 
@hd A x (@cons A a l) = match (@cons A a l) with
| nil => x
| y :: xs => y
end)).
get_definitions_theories unit ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_pattern_matching H' 1)). assumption.
Qed.


Goal ((forall (A: Type) (l : list A), 
@List.length A l = match l with
| nil => 0
| y :: xs => length xs + 1
end) -> True).
intro H.
eliminate_pattern_matching H 0.
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
eliminate_fix_hyp H.
eliminate_pattern_matching H0 1.
Abort.

Definition bool_pair := (bool * bool)%type.
Inductive dep_type : Type -> Type :=
| ToBool : bool -> dep_type bool
| ToUnit : bool -> dep_type unit.

Definition dep_fun : bool -> bool_pair -> bool := fun d : bool => match d with
                      | true => fst
                      | false => snd
                      end
.

Definition dep_match : forall (ω :  bool_pair) (a : Type) (D :  dep_type a), (match D with 
| ToBool _ =>  bool 
| ToUnit _ => unit
end) -> bool :=
fun ω a D => match D with
| ToBool d => fun x => Bool.eqb (dep_fun d ω) x
| ToUnit d => fun x => true
end.


Goal True.
get_def length. expand_hyp length_def. eliminate_fix_hyp H.  
get_def Nat.add. expand_hyp add_def. eliminate_fix_hyp H1.
eliminate_dependent_pattern_matching H2.
eliminate_dependent_pattern_matching H0.
get_def dep_match. expand_hyp dep_match_def.
eliminate_fix_hyp H0.
clear - H2. eliminate_dependent_pattern_matching H2. 
Abort. 

 Fixpoint nth {A : Type} (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

Goal False.
get_def @nth. expand_hyp nth_def. 
eliminate_fix_hyp H.  
eliminate_dependent_pattern_matching H0.
Abort.

End Tests.

















