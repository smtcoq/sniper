From elpi Require Import elpi.
Require Import List.
Import ListNotations.

Ltac my_refine T inst :=
  refine ((fun (x : T) => _) inst).
  

Elpi Tactic elimination_polymorphism.

From Sniper.elpi Extra Dependency "utilities.elpi" as Utils.
From Sniper.elpi Extra Dependency "instantiate.elpi" as Inst.
From Sniper.elpi Extra Dependency "find_instances.elpi" as FindInst.
From Sniper.elpi Extra Dependency "construct_cuts.elpi" as ConstructCuts.
Elpi Accumulate File Utils.
Elpi Accumulate File Inst.
Elpi Accumulate File FindInst.
Elpi Accumulate File ConstructCuts.

Elpi Accumulate lp:{{

 pred instances_param_indu_strategy_list i: list (pair term term), i: list (pair term (list term)), i: goal, o: list sealed-goal.
    instances_param_indu_strategy_list [P | XS] Inst (goal Ctx _ _ _TyG _ as G) GS :- 
      std.rev Ctx Ctx',
      pos_ctx_to_var_in_term Ctx' Inst Inst',
      snd P HPoly,
      instances_param_indu_strategy_aux HPoly Inst' [{{unit}}] LInst, !,
      std.map LInst (add_pos_ctx Ctx') LInst', 
      % unit is a dumb default case to eliminate useless polymorphic premise
      construct_cuts LInst' P G [G'|_],
      if (coq.ltac.open (instances_param_indu_strategy_list XS Inst) G' GS) true (instances_param_indu_strategy_list XS Inst G GS).
    instances_param_indu_strategy_list [] _ _G _.
    
  solve (goal Ctx _ TyG _ L as G) GL :- std.do! 
    [std.rev Ctx Ctx',
    collect_hypotheses_from_context Ctx HL HL1, 
    polymorphic_hypotheses HL1 HL2,
    argument_to_term L LTerm, 
    append_nodup HL2 LTerm HPoly, 
    find_instantiated_params_in_list Ctx' [TyG |HL] Inst, 
    instances_param_indu_strategy_list HPoly Inst G GL].
 

}}.
Elpi Typecheck.

Ltac clear_prenex_poly_hyps_in_context := repeat match goal with 
| H : forall (A : ?T), _ |- _ => first [ constr_eq T Set | constr_eq T Type] ; 
let T := type of H in let U := type of T in tryif (constr_eq U Prop) then try (clear H)
else fail
end.

Tactic Notation "elimination_polymorphism" uconstr_list_sep(l, ",") :=
  elpi elimination_polymorphism ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
intros A B C l f g. elimination_polymorphism. Abort. (* bug fix : the function name->gref 
does not work when there are local functionnal variables *)

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
intros. (* elimination_polymorphism. *) reflexivity. Abort. 

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

Section Tests.


Fixpoint zip {A B : Type} (l : list A) (l' : list B) :=
  match l, l' with
  | [], _ => []
  | x :: xs, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys 
  end.



Goal (forall A B C : Type,
forall (f : A -> B) (g : A -> C) (l : list A),
let f0 := fun x : A => (f x, g x) in
(forall (H7 H9 : Type) (H10 : H7 -> H9), map H10 [] = []) ->
(forall (H7 H9 : Type) (H10 : H7 -> H9) (h : H7) (l0 : list H7),
 map H10 (h :: l0) = H10 h :: map H10 l0) ->
map f0 l = zip (map f l) (map g l)).
Proof. intros.
elimination_polymorphism.
Abort.

Goal (forall A B C : Type,
forall (f : A -> B) (g : A -> C),
let f0 := fun x : A => (f x, g x) in
let f1 := @map A (B * C) f0 in
let f2 := @map A B f in
let f3 := @map A C g in
(forall (H5 H7 : Type) (l' : list H7), @zip H5 H7 [] l' = []) ->
(forall (H7 H9 : Type) (H10 : H7) (H11 : list H7), @zip H7 H9 (H10 :: H11) [] = []) ->
(forall (H7 H9 : Type) (H10 : H7) (H11 : list H7) (h : H9) (l : list H9),
 @zip H7 H9 (H10 :: H11) (h :: l) = (H10, h) :: @zip H7 H9 H11 l) ->
f1 [] = [] ->
(forall (a : A) (l : list A), f1 (a :: l) = f0 a :: f1 l) ->
f2 [] = [] ->
(forall (a : A) (l : list A), f2 (a :: l) = f a :: f2 l) ->
f3 [] = [] ->
(forall (a : A) (l : list A), f3 (a :: l) = g a :: f3 l) ->
(forall (x : Type) (x0 x1 : x) (x2 x3 : list x), x0 :: x2 = x1 :: x3 -> x0 = x1 /\ x2 = x3) ->
(forall (x : Type) (x0 : x) (x1 : list x), [] = x0 :: x1 -> False) ->
(forall (x x0 : Type) (x1 x2 : x) (x3 x4 : x0), (x1, x3) = (x2, x4) -> x1 = x2 /\ x3 = x4) ->
f1 [] = @zip B C (f2 []) (f3 [])).
Proof. intros. elimination_polymorphism. Abort.

End Tests.





