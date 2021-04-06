Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import eta_expand.
Require Import List.

Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).

MetaCoq Quote Definition unit_reif := unit.

MetaCoq Quote Definition eq_reif := Eval cbn in @eq.

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

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

Fixpoint subst_type_constructor_list (l : list ((string × term) × nat)) (T : term) :=
match l with 
| nil => nil
| ((_, Ty), _):: l' => (subst10 T Ty) :: (subst_type_constructor_list l' T)
end.


Ltac list_types_of_ctors I :=
run_template_program (tmQuoteRec I) ltac:(fun t => 
let x := eval compute in (get_decl_inductive t.2 t.1) in match x with
| Some (?y::_) => let z := eval cbv in y.(ind_ctors) in 
let v := eval cbv in t.2 in let u := eval cbv in (subst_type_constructor_list z v) in
pose u
| None => fail 1
end).


Definition list_types_of_each_constructor t :=
let x := get_decl_inductive t.2 t.1 in match x with
| Some y => match y with 
          | nil => nil
          | cons y' l => let z := y'.(ind_ctors) in let v := t.2 in let u := 
subst_type_constructor_list z v in u
          end
| None => nil
end.


Definition get_info_inductive (I : term) := 
match I with
| tInd ind inst => Some (ind, inst)
| _ => None
end.


Fixpoint get_list_of_rel (i : nat) := match i with
| 0 => []
| S n => (get_list_of_rel n) ++ [tRel n]
end.


Fixpoint get_term_applied_aux (c : term) (T : term) (acc : list term) 
 :=
(* the constructor reified c and its type, acc is the type of each arguments *)
match T with 
| tProd _ Ty Ty' => ((get_term_applied_aux c Ty' (Ty :: acc)).1, 
(get_term_applied_aux c Ty' (Ty :: acc)).2)
| _ => let n := (List.length acc) in if Nat.eqb n 0 then (c, acc) else
 (tApp c (get_list_of_rel (List.length acc)), acc)
end.

Definition get_term_applied (c : term) (T : term) := get_term_applied_aux c T [].


Definition get_term_applied_eq (c : term) (I : term) (type_of_c : term) (t' : term)
 := mkEq I (get_term_applied c type_of_c).1 t'.

Definition get_fun_with_constructor_applied_eq (f_reif : term) (c : term) (codomain : term)
(type_of_c : term) (t' : term) :=
mkEq codomain (tApp f_reif [(get_term_applied c type_of_c).1]) t'.

Fixpoint produce_trivial_eq (c : term) (type_of_c : term) 
(type_of_args : list term) (I : term) := match type_of_args with
| [] => get_term_applied_eq c I type_of_c (get_term_applied c type_of_c).1
| x :: xs => tProd {| binder_name := nAnon; binder_relevance := Relevant |} x (produce_trivial_eq c type_of_c
xs I)
end.



Definition produce_eq_tcase (f_reif : term) (c : term) (type_of_c : term) (codomain : term) 
(I : term) (case : term) := 
(*here, case is the case suitable for the given constructor c *)
let type_of_args := (get_term_applied c type_of_c).2 in 
let fix aux (f_reif : term) (c : term) (type_of_c : term) codomain (I : term) (case : term) (type_of_args : list term)
:= match type_of_args with
| [] => get_fun_with_constructor_applied_eq f_reif c codomain type_of_c (get_term_applied case type_of_c).1
| x :: xs => tProd {| binder_name := nAnon; binder_relevance := Relevant |} x (aux f_reif c type_of_c codomain I case xs)
end
in aux f_reif c type_of_c codomain I case type_of_args.


(* find the right case of a tCase given its index *)
Fixpoint find_tCase (n : nat) (t : term) := match t with
| tLambda _ _ t' => find_tCase n t'
| tCase _ _ _ l => (nth n l (0, unit_reif)).2
| _ => unit_reif
end.

Definition find_index_constructor (c : term) :=
match c with
| tConstruct _ n _ => n
| _ => 0
end.


Ltac produce_eq_tCase f c := let f_unfold := eval unfold f in f in match type of f with
| ?A -> ?B => quote_term A (fun I => quote_term B (fun codomain => 
 let type_of_c := type of c in quote_term c (fun c =>
quote_term type_of_c (fun type_of_c =>
quote_term f (fun f_reif => quote_term f_unfold (fun f_unfold_reif => 
let n := eval cbv in (find_index_constructor c) in let case := eval cbv in 
(find_tCase n f_unfold_reif) in
let x := eval cbv in (produce_eq_tcase f_reif c type_of_c codomain I case) in 
run_template_program (tmUnquote x) ltac:(fun x => let z := eval hnf in x.(my_projT2) in let H := fresh in
assert z as H ; simpl ; try reflexivity)
))))))
| _ => fail
end.



(* gets the list of constructors given an inductive recursively quoted and the number of its constructors *)
Definition get_list_ctors_tConstruct I n := 
let I' := get_info_inductive I in match I' with
| Some J => let ind := J.1 in let inst := J.2 in let fix aux n' ind' inst' :=
match n' with 
| 0 => []
| S m =>  (aux m ind' inst') ++ [tConstruct ind' m inst']
end
in aux n J.1 J.2
| None => []
end.

Ltac list_ctors_unquote_requote_rec t :=
run_template_program (tmUnquote t) (fun t => 
let x:= eval hnf in t.(my_projT2) in run_template_program (tmQuoteRec x) ltac:(fun t => 
let x:= eval cbv in (list_types_of_each_constructor t) in pose x)).


Fixpoint find_list_tCase (t : term) := match t with
| tLambda _ _ t' => find_list_tCase t'
| tCase _ _ _ l => List.map snd l
| _ => []
end.

Definition eliminate_pattern_matching (f : term) (codomain : term) (I_rec : program) 
(case : list term) := 
let I := I_rec.2 in 
let l := list_types_of_each_constructor I_rec in let n := length l in
let l' := get_list_ctors_tConstruct I n in
let fix aux f codomain l l' case I  :=
match (l , (l', case)) with
| (nil, _) | (_ , (_, nil)) | (_, (nil, _)) => nil
| (x :: xs, (y :: ys, z :: zs)) => aux f codomain xs ys zs I ++ 
[ produce_eq_tcase f y x codomain I z]
end
in aux f codomain l l' case I.


Ltac unquote_list l :=
match constr:(l) with
| nil => idtac
| cons ?x ?xs => unquote_term x ; unquote_list xs
end.


Ltac produce_eq_tCase_fun f := 
match type of f with
| ?A -> ?B => quote_term B (fun codomain => 
let f_unfold := eval unfold f in f in quote_term f_unfold (fun f_unfold_reif =>
let l := eval cbv in (find_list_tCase f_unfold_reif) in
run_template_program (tmQuoteRec A) (fun I_rec => quote_term f (fun f => 
let list := eval cbv in (eliminate_pattern_matching f codomain I_rec l) in unquote_list list))))
| _ => fail 1
end.

Definition get_fst_arg t := 
match t with
| tApp _ l => match l with 
              | nil => unit_reif
              | x :: xs => x
              end
| _ => unit_reif
end.

Definition get_snd_arg t := 
match t with
| tApp _ l => match l with 
              | [] | [ _ ]=> unit_reif
              | _ :: (y :: xs) => y
              end
| _ => unit_reif
end.

Definition get_thrd_arg t := 
match t with
| tApp _ l => match l with 
              | [] | [ _ ] | [_ ; _ ]=> unit_reif
              | _ :: (y :: ( z :: xs)) => z
              end
| _ => unit_reif
end.


Definition get_type_of_args t := 
let fix aux t (acc : list term) := match t with 
| tLambda _ ty s => aux s (ty::acc)
| tProd _ ty s => aux s (ty :: acc)
| _ => acc 
end in aux t [].

Fixpoint remove_forall t := match t with
| tProd _ _ u => remove_forall u
| _ => t
end.


Ltac unquote_requote_rec t :=
run_template_program (tmUnquote t) (fun t => 
let x:= eval hnf in t.(my_projT2) in run_template_program (tmQuoteRec x) ltac:(fun t => idtac t)).



Definition erase_forall (H : term) := match H with
| tProd _ Ty t => (Ty, t)
| _ => (unit_reif, unit_reif)
end.

Definition head (t : term) :=
match t with 
| tApp x y => x 
| _ => unit_reif 
end.



(* Simplification : H must be of the form forall x, f x = match x with ... *)
Ltac produce_eq_tCase_hyp H := 

let T := type of H in 
quote_term T (fun T => 
let eq := eval cbv in (erase_forall T).2 in 
let Ind := eval cbv in (erase_forall T).1 in 
run_template_program (tmUnquote Ind) (fun Ind => 
let x:= eval hnf in Ind.(my_projT2) in run_template_program (tmQuoteRec x) 
ltac:(fun I_rec =>  
let f_fold := eval cbv in (head (get_snd_arg eq)) in
let f_unfold_reif := eval cbv in (get_thrd_arg eq) in
let codomain := eval cbv in (get_fst_arg eq) in 
let l := eval cbv in (find_list_tCase f_unfold_reif) in
let list := eval cbv in (eliminate_pattern_matching f_fold codomain I_rec l) in unquote_list list))).


Ltac prove_hypothesis :=
 match goal with
  | H := ?x : ?P |- _ => lazymatch P with 
                | id _ => fail 
                | Prop => assert x by (try reflexivity) ; change P with (id P) in H ; clear H
             end
          end.

(* when a hypothesis is of type id Q, replaces it by Q *)
Ltac eliminate_id :=
  match goal with
    | H : ?P |- _ =>
      lazymatch P with
        | id ?Q => change P with Q in H
        | _ => fail
  end
end.

Ltac eliminate_pattern_matching_ind f :=
produce_eq_tCase_fun f ; repeat prove_hypothesis ; repeat eliminate_id.

Ltac eliminate_pattern_matching_hyp H :=
 produce_eq_tCase_hyp H ; repeat prove_hypothesis ; repeat eliminate_id.



Definition get_env (T: term) (n  : nat) := 
let fix aux T n acc := 
match (T, n) with
| (tProd _ A x, 0) => ((acc, x), A)
| (tProd _ A x, S n') => aux x n' (A::acc)
| _ => ((acc, T), T)
end
in aux T n [].

Definition type_no_app t := match t with
| tApp u l => u
| _ => t
end.


Fixpoint prenex_quantif_list (l : list term) (t : term):= 
match l with
| [] => t 
| x :: xs => prenex_quantif_list xs (mkProd x t)
end.

Definition list_of_args (t : term) := let fix aux acc t := match t with
| tProd _ t1 t2 => aux (t1 :: acc) t2
| _ => acc
end in aux [] t.


Definition prenex_quantif_list_ctor (c : term) (l : list term) (l' : list term) (E : term) :=
(* c is the constructor reified, l is the list of the type of its arguments, l' is the list of the 
type of the prenex quantification in the hypothesis, E is the environment *)
let n := Datatypes.length l in
prenex_quantif_list l' (prenex_quantif_list l (subst [tApp c (rev (get_list_of_rel n))] 0 (lift n 1 E))).

Definition get_equalities (E : term) (l_ctors : list term) (l_ty_ctors  : list term) (l_ty : list term) :=
let fix aux (E : term) (l_ctors : list term) (l_ty_ctors  : list term) (l_ty : list term) acc :=
match (l_ctors, l_ty_ctors) with
| (nil, _) | (_ , nil) => acc
| (x :: xs, y :: ys) => aux E xs ys l_ty
((prenex_quantif_list_ctor x (list_of_args y) l_ty E) :: acc)
end
in aux E l_ctors l_ty_ctors l_ty [].

(* tac H n analyse l'hypothèse H qui doit être de la forme
     forall x0, forall x1, ... forall x(k-1), E[match xi with _ end]
   et définit une contante entière nommée n de valeur i *)
Ltac tac H :=
  (* tac_rec n x k renvoie k n si le but contient un match x with _ end,
     sinon elle introduit si elle peut une variable dans le contexte et
     s'appelle récursivement en incrémentant n,
     et sinon échoue *)
  let n := fresh "n" in 
  let rec tac_rec n x k :=
    match goal with
        (* ça réussit *)
      | |- context C[match x with _ => _ end] => k n
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

Ltac eliminate_pattern_matching_debug H :=

  let n := fresh "n" in 
  let rec tac_rec n x k :=
    match goal with
      | |- context[match x with _ => _ end] => k n
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S n) y k
      | _ => fail
    end in
  evar (n : nat);
  let A := type of H in
  let H' := fresh in
  assert (H' : False -> A);
  [ let HFalse := fresh in
    intro HFalse;
    tac_rec 0 ltac:(fresh) ltac:(fun m =>
      match constr:(m) with
        | 0 => fail
        | S ?p => instantiate (n := p) 
      end);
    destruct HFalse
  | clear H' ; let T := type of H in 
quote_term T (fun T => let prod := eval cbv in (get_env T n) in
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in pose A
) ].



Ltac eliminate_pattern_matching_hyp' H :=

  let n := fresh "n" in 
  let rec tac_rec n x k :=
    match goal with
      | |- context[match x with _ => _ end] => k n
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S n) y k
      | _ => fail
    end in
  evar (n : nat);
  let A := type of H in
  let H' := fresh in
  assert (H' : False -> A);
  [ let HFalse := fresh in
    intro HFalse;
    tac_rec 0 ltac:(fresh) ltac:(fun m =>
      match constr:(m) with
        | 0 => fail
        | S ?p => instantiate (n := p) 
      end);
    destruct HFalse
  | clear H' ; let T := type of H in 
quote_term T (fun T => let prod := eval cbv in (get_env T n) in
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in
let A' := eval cbv in (type_no_app A) in
(* we need to quote AND requote recursively A*) 
run_template_program (tmUnquote A') (fun P => 
let x:= eval hnf in P.(my_projT2) in run_template_program (tmQuoteRec x) ltac:(fun A_rec =>  pose A_rec ;
let l_ty_ctors := eval cbv in (list_types_of_each_constructor A_rec) in 
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct A n) in
let list_of_hyp := eval cbv in (get_equalities E l_ctors l_ty_ctors l) in
unquote_list (* unquote_list *) list_of_hyp
)))].

MetaCoq Quote Recursively Definition list_reif:= Datatypes.list.
Print list_reif.

Definition min1 (x : nat) := match x with
| 0 => 0
| S x => x
end.
Definition min1' := min1.

Definition min1'' := min1'.

Definition min1''' := min1''.

Goal (forall (a : nat) (b : nat) (c : nat), match b with 0 => a | S _ => c end = 0) -> True.
intro H.
tac H. (* n = 1 *)
exact I.
Qed.

Goal True.
Proof. 
eta_expand_fun min1.
eta_expand_fun hd.
eliminate_pattern_matching_hyp' H.
eliminate_pattern_matching_hyp' H0.

exact I.
Qed.










