From elpi Require Import elpi.
Require Import List.

Elpi Tactic elimination_polymorphism.
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate File "elpi/instantiate.elpi".
Elpi Accumulate File "elpi/find_instances.elpi".
Elpi Accumulate File "elpi/construct_cuts.elpi".

Elpi Accumulate lp:{{

 pred instances_param_indu_strategy_list i: list (pair term term), i: list (pair term (list instance)), i: goal, o: list sealed-goal.
    instances_param_indu_strategy_list [P | XS] Inst (goal Ctx _ _ _ _ as G) GS :- std.rev Ctx Ctx',
      subst_in_instances Ctx' Inst Inst',
      snd P HPoly,
      instances_param_indu_strategy_aux HPoly Inst' [{{unit}}] LInst, !,
      % unit is a dumb default case to eliminate useless polymorphic premise
      construct_cuts LInst ProofTerm,
      refine ProofTerm G GL1, !,
      refine_by_instantiation GL1 P [G1|_GL], !, 
      coq.ltac.open (instances_param_indu_strategy_list XS Inst) G1 GS.
    instances_param_indu_strategy_list [] _ _G _.
    
  solve (goal Ctx _ TyG _ L as G) GL :- std.rev Ctx Ctx',
    collect_hypotheses_from_context Ctx HL HL1, polymorphic_hypotheses HL1 HL2, argument_to_term L LTerm, 
    append_nodup HL2 LTerm HPoly, !, find_instantiated_params_in_list Ctx' [TyG |HL] Inst, 
    instances_param_indu_strategy_list HPoly Inst G GL.
 

}}.
Elpi Typecheck.

Ltac clear_prenex_poly_hyps_in_context := repeat match goal with 
| H : forall (A : ?T), _ |- _ => first [ constr_eq T Set | constr_eq T Type] ; 
let T := type of H in let U := type of T in tryif (constr_eq U Prop) then try (clear H)
else fail
end.

Tactic Notation "elimination_polymorphism" uconstr_list_sep(l, ",") :=
  elpi elimination_polymorphism ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context.

Goal forall (l : list nat) (p: bool * nat), l = l.
Proof. intros. elpi elimination_polymorphism (app_length) (pair_equal_spec) (app_cons_not_nil). 
intros. elpi elimination_polymorphism (pair_equal_spec).
Abort.

Goal (forall (A : Type) (l : list A), A = A) -> (forall (B: Type), B = B) ->
(1 + 1 = 2) -> (forall (A : Type)
(l: list A) (p : A *A), l= l /\ p =p).
intros H H1 H2 A l p. elimination_polymorphism. Abort. 


(* Instances when we only look at constructors *)
Goal (forall (A: Type), list A -> False).
intros. assert (H1: forall A, List.nth_error (@nil A) 0 = None) by auto.
elimination_polymorphism. assert (H2: @nth_error A (@nil A) 0 = @None A) by assumption. Abort.

Goal (forall (A : Type), 1 = 1) -> 1=1.
Proof. intros. elimination_polymorphism. Abort.


Lemma test_clever_instances : forall (A B C D E : Type) (l : list A) (l' : list B)
(p : C * D) (p' : D*E), l = l -> l' = l' -> p = p -> (forall (A : Type) (x : A), x= x)
-> (forall (A : Type) (l : list A), l = l) -> (forall (A B : Type) (p : A *B), p =p ) ->
p' = p'.
intros. elimination_polymorphism app_length. reflexivity. Qed. 

Goal False.
pose (x := fun (A : Type) (x : A) => x).
elimination_polymorphism. Abort.

(* Test polymorphism *) 
Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> ((forall (x1 x2 : bool) (y1 y2 : nat), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : nat) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : bool) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
intro H. elimination_polymorphism. split. assumption. split. assumption. assumption.
Qed. 



