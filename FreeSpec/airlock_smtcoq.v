Require Import sniper.
Require Import List.

Print combine.

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

Definition list_types_of_each_constructor_no_subst t :=
let v := (type_no_app t.2) in (* the inductive not applied to its parameters and the list of its parameters *)
let x := get_decl_inductive v.1 t.1 in (* the first inductive declaration in a mutual inductive block  *)
let n := get_npar_inductive v.1 t.1 in  (* numbers of parameters *)
match x with
| Some y => match y with 
          | nil => nil
          | cons y' _ => let z := y'.(ind_ctors) in List.map (fun p => subst10 v.1 p.1.2) z
          end
| None => nil
end.


Fixpoint codomain (t : term) := match t with 
| tProd _ _ u => codomain u 
| _ => t 
end.


Definition build_ctor_ty_ctor_applied_to_parameters (args_in_statement : list term) (p : term * term) := let ctor := p.1 in let ty_ctor := p.2 in 
let ty_args := (type_no_app (codomain ty_ctor)).2
in let fix aux args_in_statement ty_args ctor ty_ctor := match args_in_statement, ty_args with
| nil, _ => (ctor, ty_ctor)
| _, nil => (ctor, ty_ctor)
| x_in_statement :: args_in_statement', x_in_ty :: ty_args' =>  match x_in_ty with 
        | tRel k => aux args_in_statement' ty_args' (tApp ctor [x_in_statement]) (tApp ty_ctor [x_in_statement])
        | _ => aux args_in_statement' ty_args' ctor ty_ctor
        end 
end
in aux args_in_statement ty_args ctor ty_ctor.
        


(* Definition list_types_of_each_constructor t :=
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
end. *)



Definition get_info_inductive (I : term) := 
let p := type_no_app I in match p.1 with
| tInd ind inst => Some (ind, inst)
| _ => None
end.


Fixpoint get_list_of_rel (i : nat) := match i with
| 0 => []
| S n => ((get_list_of_rel n) ++ [tRel n])%list (* n *)
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



Ltac eliminate_pattern_matching_test H :=

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
let l_ty_ctors := eval cbv in (list_types_of_each_constructor_no_subst (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct A n) in pose l_ctors as ctor ; 
let l_ctor_and_ty_ctor := eval cbv in (combine l_ctors l_ty_ctors) in let l_ctor_and_ty_ctor :=
eval cbv in (List.map (build_ctor_ty_ctor_applied_to_parameters (type_no_app A).2) l_ctor_and_ty_ctor) in
pose l_ty_ctors as ty_ctor ;
let list_of_hyp := eval cbv in (get_equalities E l_ctor_and_ty_ctor l) in
unquote_list list_of_hyp)].



Section airlock1.


Definition interface := Type -> Type.
Variable ix : interface.
Variable A B : Type.
Variable MayProvide
     : interface -> interface -> Type.
Variable Provide : forall ix i : interface, MayProvide ix i -> Type.
Definition Ω := (bool * bool)%type.
Inductive door : Set :=  left : door | right : door.
Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.
MetaCoq Quote Recursively Definition DOORS_reif := DOORS.

Compute list_types_of_each_constructor_no_subst DOORS_reif.
Inductive foo : interface := bar1 : foo A | bar2 : foo B.
Definition sel : door -> Ω -> bool := fun d : door => match d with
                      | left => fst
                      | right => snd
                      end
.
Definition co := fun d : door => match d with
                     | left => right
                     | right => left
                     end.
Inductive doors_o_caller : Ω -> forall a : Type, DOORS a -> Prop :=
    req_is_open : forall (d : door) (ω : Ω), doors_o_caller ω bool (IsOpen d)
  | req_toggle : forall (d : door) (ω : Ω),
                 (sel d ω = false -> sel (co d) ω = false) -> doors_o_caller ω unit (Toggle d).

Inductive doors_o_callee : Ω -> forall a : Type, DOORS a -> a -> Prop :=
    doors_o_callee_is_open : forall (d : door) (ω : Ω) (x : bool),
                             sel d ω = x -> doors_o_callee ω bool (IsOpen d) x
  | doors_o_callee_toggle : forall (d : door) (ω : Ω) (x : unit), doors_o_callee ω unit (Toggle d) x.

Definition doors_o_callee2 :  Ω -> forall (a : Type) (D :  DOORS a), (match D with 
| IsOpen _ =>  bool 
| Toggle _ => unit
end) -> bool :=
fun ω a D => match D with
| IsOpen d => fun x => Bool.eqb (sel d ω) x
| Toggle d => fun x => true
end.

Definition doors_o_caller2 : Ω -> forall (a : Type) (D : DOORS a), bool := 
fun ω a D => match D with
| IsOpen _ => true
| Toggle d => implb (negb (sel d ω)) (negb (sel (co d) ω))
end.


(* Variable H : MayProvide ix DOORS.
Variable H0 : Provide ix DOORS H. *)
Variable ω : Ω.
Variable d : door.

 

(* TODO : doors_o_caller doit devenir une fonction dans bool
corriger instanciate_type_tuple de manière à ce qu'il laisse 
intact les lemmes qu'il n'a pas besoin d'instancier, et on peut forcer à ce que le type du type des paramètres 
du tuple soit bien Prop *)


Goal doors_o_caller ω bool (IsOpen d).
Proof. 
scope req_is_open. 
Abort.

Goal forall H d x, doors_o_callee2 H bool (IsOpen d) x = Bool.eqb (sel d ω) x.
Proof. 
scope. Check Toggle. eliminate_pattern_matching_test H1. Abort.

Goal doors_o_caller2 ω (IsOpen d).
Proof. snipe. admit. admit. admit. Admitted.







(* TODO : problème avec le pattern matching quand le type de la variable sur laquelle on matche admet des indices 
(ok pour les paramètres) *)

Variable o_caller : doors_o_caller2 ω (IsOpen d).
Variable x : bool.
Variable o_caller0 : doors_o_callee2 ω (IsOpen d) x.
Variable equ_cond : x = true.

Goal doors_o_caller2 ω (Toggle d).
Proof. scope.
clear - o_caller0 H11 equ_cond.

 (* verit *) (* verit a bien trouvé la preuve mais le parser a un problème *)

Admitted.

(* TODO : Chantal *)

Definition tog (d : door) (ω : Ω) : Ω :=
  match d with
  | left => (negb (fst ω), snd ω)
  | right => (fst ω, negb (snd ω))
  end.

Variable H1 : doors_o_callee2 ω (IsOpen d) true.
Variable x1 : unit.
Variable H2 : doors_o_callee2 ω (Toggle d) x1.

Goal sel d (tog d ω) = false.
Proof. scope.



 assert (forall (H : Ω) (d : door) (H2 : bool),
     doors_o_callee2 H (IsOpen d) H2 = Bool.eqb (sel d H) H2) by reflexivity.
assert (forall (H : Ω) (d: door) (H2 : unit),
     doors_o_callee2 H (Toggle d) H2 = true) by reflexivity.
clear - H6 H7 H8 H9 H12 H13 H11. (* je crois qu'on a besoin d'une analyse de cas sur ω *)
Admitted.


Variable ω' : Ω.
Variable Hyp : doors_o_callee2 ω' (IsOpen d) false.

Goal sel d ω' = false.
Proof. scope. clear - H9 Hyp. (* verit. *)

specialize (H9 ω' d). specialize (H9 false). unfold is_true in Hyp.
rewrite Hyp in H9. clear - H9. verit. admit. admit.
 (* Pourquoi verit n'a pas pu résoudre le but ??? *)
Admitted.  


End airlock1. 

Section airlock2. 
Variable ix : Type.
Variable i1 i2 : Type.
Variable MayProvide
     : Type -> Type -> Type.
Variable Provide : forall ix i : Type, MayProvide ix i -> Type.

Variable Distinguish
     : forall (ix i j : Type) (H : MayProvide ix i), Provide ix i H -> MayProvide ix j -> Prop.

Variable StrictProvide2
     : forall (ix i1 i2 : Type) (H : MayProvide ix i1) (H0 : Provide ix i1 H)
         (H1 : MayProvide ix i2) (H2 : Provide ix i2 H1),
       Distinguish ix i1 i2 H H0 H1 -> Distinguish ix i2 i1 H1 H2 H-> Prop.
Inductive STORE : Type :=  Get : Type -> STORE | Put : STORE.

Variable H : MayProvide ix DOORS.
Variable H0 : Provide ix DOORS H.
Variable H1 : MayProvide ix (STORE).
Variable H2 : Provide ix (STORE) H1.
Variable H3 : Distinguish ix DOORS (STORE) H H0 H1.
Variable H4 : Distinguish ix (STORE) DOORS H1 H2 H.


Notation "m '~>' n" := (forall (α : Type) (_ : m α), n α) (at level 50).

Inductive impure (i : Type) (α : Type) : Type :=
    local : α -> impure i α | request_then : forall β : Type, i -> (β -> impure i α) -> impure i α.

Variable contract
     : Type -> Type -> Type.
Definition component :=
    fun i j : Type => i -> j.
Variable no_contract
     : forall i : Type, contract i unit.
Variable doors_contract
     : contract DOORS Ω.
Variable correct_component: forall jx j : Type,
       MayProvide jx j ->
       forall i : Type,
       component i jx ->
       forall Ωi : Type,
       contract i Ωi -> forall Ωj : Type, contract j Ωj -> (Ωi -> Ωj -> Prop) -> Prop.
Inductive CONTROLLER : Type :=  Tick : CONTROLLER | RequestOpen : door -> CONTROLLER.
Inductive iplus (i j : Type) : Type :=
    in_left : i -> iplus i j | in_right : j -> iplus i j.

Variable controller
     : component CONTROLLER (iplus (STORE) DOORS). (* TODO *)
Record hoare (Σ α : Type) : Type := mk_hoare { pre : Σ -> Prop;  post : Σ -> α -> Σ -> Prop }.



(*  Corresponds to return and bind *)
Variable to_hoare : forall ix i : Type,
       MayProvide ix i -> forall Ω : Type, contract i Ω -> impure ix ~> hoare Ω.

Variable ωc : unit.
Variable ωd : Ω.
Variable close_door : 
forall (ix : Type) (H : MayProvide ix DOORS), Provide ix DOORS H -> door -> impure ix unit.
Variable open_door : forall (ix : Type) 
(H : MayProvide ix DOORS), Provide ix DOORS H -> door -> impure ix unit.


Goal pre Ω unit (@to_hoare ix DOORS H Ω doors_contract unit (close_door ix H H0 left)) ωd.
Proof.
(* interp_alg_types_context_goal. *) (* bug de la tactique de Pierre *)
def_fix_and_pattern_matching.
Fail timeout 30 verit.
Admitted.


Variable ω : Ω.
Variable d : door.



Goal pre Ω unit (to_hoare ix DOORS H Ω doors_contract unit (close_door ix H H0 right)) ω.
def_fix_and_pattern_matching. clear H7.
Fail verit.
Admitted.

Goal pre Ω unit (to_hoare ix DOORS H Ω doors_contract unit (close_door ix H H0 (co d))) ωd.
def_fix_and_pattern_matching. Fail verit. Admitted.

Goal pre Ω unit (to_hoare ix DOORS H Ω doors_contract unit (open_door ix H H0 d)) ω.
Admitted.

Variable a : Type.
Variable e : CONTROLLER.
Variable callee_obligation
     : forall (i : Type) (Ω : Type), contract i Ω -> Ω -> forall α : Type, i -> α -> Prop.
Variable controller2 :
    forall (ix : Type) (H : MayProvide ix DOORS),
       Provide ix DOORS H ->
       forall H1 : MayProvide ix (STORE), Provide ix (STORE) H1 -> component CONTROLLER ix.
Variable caller_obligation
     : forall (i : Type) (Ω : Type), contract i Ω -> Ω -> i -> Prop.
Variable req : caller_obligation CONTROLLER unit (no_contract CONTROLLER) ωc e.
Variable hpre : pre Ω a (to_hoare ix DOORS H Ω doors_contract a (controller2 ix H H0 H1 H2)) ωd.
Goal and (pre Ω a (to_hoare ix DOORS H Ω doors_contract a (controller2 ix H H0 H1 H2 a e)) ωd)
  (forall (x : a) (ωj' : Ω)
     (_ : post Ω a (@to_hoare ix DOORS H Ω doors_contract a (controller2 ix H H0 H1 H2 a e)) ωd x
            ωj'),
   and (callee_obligation CONTROLLER unit (no_contract CONTROLLER) ωc a e x)
     (or (eq bool (sel left ωj') false) (eq bool (sel right ωj') false))).
































