Require Import sniper.
Require Import List.
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

Print DOORS_ind.

MetaCoq Quote Recursively Definition DOORS_ind_reif := DOORS_ind.


Print DOORS_ind_reif.

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

Goal forall x: DOORS bool, x = IsOpen left.
intro x. inversion x. admit. 
assert (exists (x1 x2 : unit), x1 <> x2).
rewrite H. exists true, false. discriminate.
destruct H1. destruct H1. destruct x0. destruct x1. 
elim H1. reflexivity.
Abort.

Goal True.
epose (foo := ?[foo_evar] : Prop).
instantiate (foo_evar := True). assert foo. exact I.
exact I. Qed.

Goal forall H d x, doors_o_callee2 H bool (IsOpen d) x = Bool.eqb (sel d ω) x.
Proof. 
scope. clear -H1. 



assert (H2 : forall (H : Ω) (H0 : Type) (H1 : DOORS H0)
       (H2 : match H1 with
             | IsOpen _ => bool
             | Toggle _ => unit
             end),
     doors_o_callee2 H H0 H1 H2 =
     match
       H1 as D in (DOORS T) return (match D with
                                    | IsOpen _ => bool
                                    | Toggle _ => unit
                                    end -> bool)
     with
     | IsOpen d => fun x : bool => (sel d H <---> x)%bool
     | Toggle _ => fun _ : unit => true
     end H2).
intros H0 H2 H3. case H3. clear H3. revert H0 H2. (* processus pour récupérer le but que l'on cherche *)
intros. apply H1. 




 Abort.

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
































