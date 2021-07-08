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

Lemma n' : nat.
exact 0.
Qed.

MetaCoq Quote Definition n'_reif := n'.
Print n'_reif.

Goal True.
let x := metacoq_get_value (tmQuoteRec bool) in idtac x.
let x := metacoq_get_value (tmQuote bool) in idtac x.
let x := metacoq_get_value (tmQuoteInductive (MPfile ["Datatypes"; "Init"; "Coq"], "bool")) in idtac x. 
let x := metacoq_get_value (tmQuoteConstant (MPfile ["tacpattern"; "FreeSpec"; "Sniper"], "n'") true) in idtac x.
let x := metacoq_get_value (tmQuoteConstant (MPfile ["tacpattern"; "FreeSpec"; "Sniper"], "n'") false) in idtac x. 
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

Ltac create_evars_for_each_constructor_test i := 
let y := metacoq_get_value (tmQuoteRec i) in 
let n:= eval cbv in (get_nb_constructors y.2 y.1) in
let rec tac_rec u := match constr:(u) with 
      | 0 => idtac
      | S ?m => let H' := fresh in let H'_evar := fresh H' in epose (H' := ?[H'_evar] : Prop) ; idtac H' ; tac_rec m
end in tac_rec n.

Goal True.

create_evars_for_each_constructor bool.
create_evars_for_each_constructor unit.
create_evars_for_each_constructor nat.
create_evars_for_each_constructor_test nat.
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

Print head_tuple.
Compute head_tuple _ _ (1, tt).


Definition tail_tuple (A B : Type) (x : A*B) := match x with
|(y, z) => z
end.


Lemma test_revert_tuple : forall (A B : Type) (C : A) (n n' : nat) (x : bool), x = x.
intros. revert_tuple (A, B, C, n'0, n', x, unit). reflexivity. Qed. (*  unit in first *)

Ltac detect_var_match H :=

let T := type of H in 
let H' := fresh in 
assert (H' : False -> T) by
(match goal with | |-context C[match ?x with _ => _ end] => idtac x end; let Hfalse := fresh in 
intro Hfalse; destruct Hfalse) ; clear H' ; idtac.


(* tac H n analyse l'hypothèse H qui doit être de la forme
     forall x0, forall x1, ... forall x(k-1), E[match xi with _ end]
   et définit une constante entière nommée n de valeur i *)
Ltac tac H n :=
  (* tac_rec n x k renvoie k n si le but contient un match x with _ end,
     sinon elle introduit si elle peut une variable dans le contexte et
     s'appelle récursivement en incrémentant n,
     et sinon échoue *)
  let rec tac_rec n x k :=
    match goal with
        (* ça réussit *)
      | |- context[match x with _ => _ end] => k n
        (* on introduit une variable et on appelle récursivement avec
           le nom de cette variable et en incrémentant le premier paramètre *)
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S n) y k
      | _ => fail
    end in
  (* cette evar sert à transmettre un resultat dans l'autre but qui sera généré *)
  evar (n : nat);
  let A := type of H in
  let H' := fresh in
  (* on crée artificiellement un but trivial à partir de l'hypothèse *)
  assert (H' : False -> A);
  [ let HFalse := fresh in
    intro HFalse;
    (* on appelle tac_rec avec 0, une variable fraîche (qui ne peut donc
       pas apparaître dans H) et une continuation bien choisie *)
    tac_rec 0 ltac:(fresh) ltac:(fun m =>
      match constr:(m) with
          (* ce cas ne peut pas arriver car on a passé une variable fraîche à tac_rec *)
        | 0 => fail
          (* c'est le cas qui réussit, on instantie alors n *)
        | S ?p => instantiate (n := p)
      end);
    destruct HFalse (* on ferme le premier sous-but *)
  | clear H' (* on efface l'hypothèse qui a été rajoutée *) ].

Goal (forall (a : nat) (b : nat) (c : nat), match a with 0 => a | S _ => c end = 0) -> True.
intro H.
tac H n. (* n = 0 *)
exact I.
Qed.

Goal (forall (a : nat) (b : nat) (c : nat), match b with 0 => a | S _ => c end = 0) -> True.
intro H.
tac H n. (* n = 1 *)
exact I.
Qed.

Goal (forall (a : nat) (b : nat) (c : nat), match c with 0 => a | S _ => c end = 0) -> True.
intro H.
tac H n. (* n = 2 *)
exact I.
Qed.

Goal (forall (a : nat) (b : nat) (c : nat), match 3 + 4 with 0 => a | S _ => c end = 0) -> True.
intro H.
Fail tac H n. (* le match n'est pas sur une variable *)
exact I.
Qed.

Goal (forall (a : nat) (b : nat) (c : nat), match b + c with 0 => a | S _ => c end = 0) -> True.
intro H.
Fail tac H n. (* le match n'est pas sur une variable *)
exact I.
Qed.

Goal (forall (a : nat) (b : nat) (c : nat), 0 = 0) -> True.
intro H.
Fail tac H n. (* il n'y a pas de match *)
exact I.
Qed.

Goal (forall (a : nat) (b : nat) (c : nat), (forall d : nat, match d with 0 => a | S _ => c end = 0) -> False) -> True.
intro H.
Fail tac H n. (* le match est sur une variable qui n'est pas quantifiée de manière prénexe *)
exact I.
Qed.

Goal (forall (a : nat) (b : nat) (c : nat), (forall d : nat, match b with 0 => a | S _ => c end = 0) -> False) -> True.
intro H.
tac H n. (* n = 1 *)
exact I.
Qed.

Goal forall x : nat, (forall (a : nat) (b : nat) (c : nat), match x with 0 => a | S _ => c end = 0) -> True.
intros x H.
Fail tac H n. (* le match est sur une variable qui n'est pas quantifiée de manière prénexe *)
exact I.
Qed.

Ltac remove_app t :=
lazymatch constr:(t) with 
| ?u ?v => remove_app u 
| _ => t
end.

Goal forall (A : Type) (x: list A), x = x.
Proof. intros. let T := type of x in let T' := remove_app T in idtac T'.
reflexivity.
Qed.

Ltac eliminate_pattern_matching H :=

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
let var_match := eval cbv in (head_tuple _ _ t) in idtac var_match ;
let var_to_revert := eval cbv in (tail_tuple _ _ t) in idtac var_to_revert ;
case var_match ; try (clear var_match) ; revert_tuple var_to_revert ;
match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse' end)
; clear foo ; 
repeat match goal with 
| u : Prop |-_ => let u' := eval unfold u in u in assert u' by 
( intros; try (apply H); reflexivity); clear u end] ; clear H ; 
clear n; clear T.

Ltac eliminate_pattern_matching_destruct H :=

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
let t := intro_and_tuple nb_var in idtac t ;
let var_match := eval cbv in (head_tuple _ _ t) in
let var_to_revert := eval cbv in (tail_tuple _ _ t) in
destruct var_match ; revert_tuple var_to_revert ; 
repeat match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse' end)
; clear foo ; 
repeat match goal with 
| u : Prop |-_ => let u' := eval unfold u in u in assert u' by 
( intros; now (eapply H; reflexivity)); clear u end] ; clear H ; 
clear n; clear T.

Print binder_name.

Definition mkProdName na T u :=
tProd {| binder_name := nNamed na ; binder_relevance := Relevant |} T u.

Check mkProdName.



MetaCoq Quote Definition eq_reif_nat := (@eq nat).


MetaCoq Quote Definition toto := (forall (x: nat), x = x).



Definition foo := mkProdName "x" nat_reif (mkProdName "x" nat_reif (tApp eq_reif_nat [tRel 0; tRel 1]) ) .

Eval compute in toto.
Eval compute in foo.

MetaCoq Unquote Definition bar := foo.

Print bar.

Print toto.


Ltac revert_count := 
let rec revert_count_rec n :=
match goal with
| H : _ |- _ => let _ := match goal with _ => revert H end in revert_count_rec (S n)
| _ => n
end in revert_count_rec 0.


Goal True -> True -> False -> True -> False.
intros.
let n := revert_count in pose n.
auto. Qed.

Ltac hyps := 
match goal with
| H : _ |- _ => let _ := match goal with _ => revert H end in let acc := hyps in 
let _ := match goal with _ => intro H end in constr:((H, acc))
| _ => constr:(unit)
end.

Goal True -> True -> False -> True -> False.
intros. let k := hyps in idtac k.
Abort.

Ltac clear_if_in_term p t := 
match p with 
| (?x, ?y) => match t with 
              | context [x] => try (clear x) 
              | _ => idtac end ; clear_if_in_term y t 
| unit => idtac
end.

Ltac eliminate_pattern_matching_case H :=

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
let var_match := eval cbv in (head_tuple _ _ t) in idtac var_match ;
let var_to_revert := eval cbv in (tail_tuple _ _ t) in idtac var_to_revert ;
case var_match ; 
let indu' := type of var_match in clear var_match ; 
revert_tuple_clear var_to_revert indu' ;
match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse' end)
; clear foo ; 
repeat match goal with 
| u : Prop |-_ => let u' := eval unfold u in u in assert u' by 
( intros; try (apply H); reflexivity); clear u end] ; clear H ; 
clear n; clear T.


Goal True.
get_def length. expand_hyp length_def. eliminate_fix_hyp H.  
get_def Nat.add. expand_hyp add_def. eliminate_fix_hyp H1.



eliminate_pattern_matching_case H2.

eliminate_pattern_matching H0.
get_def doors_o_callee2. expand_hyp doors_o_callee2_def.
eliminate_fix_hyp H0.
clear - H2. eliminate_pattern_matching_case H2. 
Abort. 




Goal True.
get_def length. expand_hyp length_def. eliminate_fix_hyp H.  
get_def Nat.add. expand_hyp add_def. eliminate_fix_hyp H1.
 Abort. 


