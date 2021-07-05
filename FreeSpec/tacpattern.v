Require Import sniper.
From MetaCoq Require Import All.

Ltac metacoq_get_value p :=
  let id := fresh in
  let _ := match goal with _ => run_template_program p
  (fun t => pose (id := t)) end in
  let x := eval cbv delta [id] in id in
  let _ := match goal with _ => clear id end in
  x.
Print kername.

MetaCoq Quote Definition bool_reif := bool.
Print bool_reif.

Lemma n : nat.
exact 0.
Qed.

MetaCoq Quote Definition n_reif := n.
Print n_reif.

Goal True.
let x := metacoq_get_value (tmQuoteRec bool) in idtac x.
let x := metacoq_get_value (tmQuote bool) in idtac x.
let x := metacoq_get_value (tmQuoteInductive (MPfile ["Datatypes"; "Init"; "Coq"], "bool")) in idtac x. 
let x := metacoq_get_value (tmQuoteConstant (MPfile ["tacpattern"; "FreeSpec"; "Sniper"], "n") true) in idtac x.
let x := metacoq_get_value (tmQuoteConstant (MPfile ["tacpattern"; "FreeSpec"; "Sniper"], "n") false) in idtac x. 
let x := metacoq_get_value (tmQuote 0) in let y := metacoq_get_value (tmUnquote x) in idtac y.
let x := metacoq_get_value (tmQuote 0) in let y := metacoq_get_value (tmUnquoteTyped nat x) in idtac y.
Abort.

Print lookup_env.
Print Ast.

MetaCoq Quote Definition nat_reif := nat.

Print nat_reif.


Definition get_nb_constructors i Σ := 
match i with 
| tInd indu _ => match lookup_env Σ indu.(inductive_mind) with
                | Some (InductiveDecl decl) => match ind_bodies decl with 
                          | nil => 0
                          | x :: _ => length (ind_ctors x)
                          end
                | _ => 0
end
| _ => 0
end.

MetaCoq Quote Recursively Definition list_reif_rec := list.

Compute get_nb_constructors list_reif_rec.2 list_reif_rec.1.



(* Ltac get_nb_constructors_tac i k :=
run_template_program (tmQuoteRec i) ltac:(fun i_reif_rec => 
k constr:(get_nb_constructors i_reif_rec.2 i_reif_rec.1)). *)

Ltac get_nb_constructors_tac i id :=
run_template_program (tmQuoteRec i) ltac:(fun i_reif_rec => let n := 
eval cbv in (get_nb_constructors i_reif_rec.2 i_reif_rec.1) in
pose (id := n)).

(* NOTE : il faut donner en paramètre de la continuation une vraie tactique c'est à dire une pas 
value_tactic *)


Goal True.
get_nb_constructors_tac bool ident:(foo).
exact I. Qed.


Goal False.
let H := fresh in get_nb_constructors_tac bool H.
Abort.


Ltac create_evars_for_each_constructor i := 
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
Abort.

Lemma dummy_length : forall A (l : list A), length l = match l with | nil => 0 | cons x xs => S (length xs) end.
intros. destruct l; simpl;  reflexivity. Qed.

Lemma test_length: (False -> forall A (l : list A), length l = match l with | nil => 0 | cons x xs => S (length xs) end) 
/\ True.
Proof. create_evars_for_each_constructor list. split.
intros Hfalse A l. case l; try clear l; revert A; 
match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse end.
repeat match goal with 
| u : Prop |-_ => let u' := eval unfold u in u in assert u' by ( intros; apply dummy_length) ; clear u end.
exact I. 
Qed. 

Definition interface := Type -> Type.
Definition Ω := (bool * bool)%type.
Inductive door : Set :=  left : door | right : door.
Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Definition sel : door -> Ω -> bool := fun d : door => match d with
                      | left => fst
                      | right => snd
                      end
.

Definition doors_o_callee2 : forall (ω :  Ω) (a : Type) (D :  DOORS a), (match D with 
| IsOpen _ =>  bool 
| Toggle _ => unit
end) -> bool :=
fun ω a D => match D with
| IsOpen d => fun x => Bool.eqb (sel d ω) x
| Toggle d => fun x => true
end.

Lemma dummy_doors : 
doors_o_callee2 =
fun ω a D => match D with
| IsOpen d => fun x => Bool.eqb (sel d ω) x
| Toggle d => fun x => true
end.
unfold doors_o_callee2. reflexivity. Qed.


Lemma test_door : (False -> forall (ω: Ω) (a : Type) (D :  DOORS a) (u: match D with 
| IsOpen _ =>  bool 
| Toggle _ => unit
end), doors_o_callee2 ω a D = match D with
| IsOpen d => fun x => Bool.eqb (sel d ω) x
| Toggle d => fun x => true
end) /\ True.
create_evars_for_each_constructor DOORS; split. intro Hfalse. intros ω a D u ; case D ;
try clear D; revert a D u; 
match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse end; repeat match goal with 
| u : Prop |-_ => let u' := eval unfold u in u in assert u' by ( intros; try (apply dummy_doors); reflexivity); clear u end.

exact I. Abort. 

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


Lemma test_intro_and_tuple :  forall (A B : Type) (C : A) (n n' : nat) (x : bool), x = x.
let p := intro_and_tuple 4 in pose (p0 := p). reflexivity. Qed.


Ltac create_evars_and_inst n := 
create_evars_and_inst_rec n (@nil nat).

Goal True.

let l:= (create_evars_and_inst_rec 4 (@nil nat)) in pose l. (* comportement super bizarre quand on enlève le repeat *) 
let l:= (create_evars_and_inst 4) in pose l.
repeat match goal with | u : nat |-_ => instantiate (u := 0) end. 
(* comportement super bizarre quand on enlève le repeat, une variable n'est jamais instanciée *)
exact I. 
Abort.

Lemma test_intros : forall (A B : Type) (C : A) (n n' : nat) (x : bool), x = x.
Proof.
let n := constr:(3) in let rec tac_rec n := match n with
| 0 => let u := fresh in intro u
| S ?m => let H := fresh in intro H ; tac_rec m
end in tac_rec n. revert H2 H1. revert H0 H. (* type dépendant = revert un par un, automatiser le revert peut-être *)



let n := constr:(4)  in let id := intro_and_return_last_ident n in idtac id. reflexivity.  Qed.


Ltac revert_tuple p := 
lazymatch constr:(p) with
| (?x, ?y) => try (revert y); revert_tuple x 
| _ => try (revert p)
end.

Definition head_tuple (A B : Type) (x : A*B) := match x with
|(y, z) => y
end.

Definition tail_tuple (A B : Type) (x : A*B) := match x with
|(y, z) => z
end.


Lemma test_revert_tuple : forall (A B : Type) (C : A) (n n' : nat) (x : bool), x = x.
intros. revert_tuple (A, B, C, n0, n', x, unit). reflexivity. Qed. (*  unit in first *)


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
                                    | S ?p => instantiate (n_evar := p) ; let Indu := type of x in 
create_evars_for_each_constructor Indu ; assert 
(False -> H) ; [let Hfalse' := fresh in intro Hfalse' ; 
let t := intro_and_tuple p in 
let var_match := eval cbv in (head_tuple t) in
let var_to_revert := eval cbv in (tail_tuple t) in
case var_match ; try (clear var_match) ; revert_tuple var_to_revert ;
repeat match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse' end] ; repeat match goal with 
| u : Prop |-_ => let u' := eval unfold u in u in assert u' by ( intros; try (apply H); reflexivity); clear u end
                                    end
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail
    end 
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ] ; clear H.



Goal False.
get_def length. expand_hyp length_def. eliminate_fix_hyp H. 
eliminate_pattern_matching H0.


