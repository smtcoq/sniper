From Sniper Require Import utils.utilities.
Require Import expand.
Require Import elimination_fixpoints.
Require Import elimination_pattern_matching.
Require Import anonymous_functions.

From elpi Require Import elpi.

Ltac mypose_elpi t := 
tryif (is_local_def t) then idtac else
let t' := 
  match t with
  | ?u ?v =>
        match goal with
        | x := v |- _ => constr:(u x)
        | _ => t
        end
  | _ => t
  end in
tryif (is_local_def t') then idtac else
let Na := fresh "f" in pose t as Na ; (* HACK : fold local def eagerly in order 
to avoid unification failures with the fixpoint transformation *)
  match t with
  | ?u ?v =>
        match goal with
        | x := v |- _ => try (fold x in Na)
        | _ => idtac
        end
  | _ => idtac 
  end.

Elpi Tactic applied_higher_order_and_polymorphic.

From Sniper.elpi Extra Dependency "utilities.elpi" as Utils.
From Sniper.elpi Extra Dependency "subterms.elpi" as Subterms.
From Sniper.elpi Extra Dependency "applied_higher_order_and_polymorphic.elpi" as AppliedHigherOrderAndPolymorphic.
Elpi Accumulate File Utils.
Elpi Accumulate File Subterms.
Elpi Accumulate File AppliedHigherOrderAndPolymorphic.

Elpi Accumulate lp:{{

  pred mypose_list i: list (pair term (list term)), i: goal, o: list sealed-goal.
  mypose_list [pr X L |XS] (goal Ctx _ _ _ _ as G) GL :- 
    std.rev Ctx Ctx',
    std.map L (elim_pos_ctx Ctx') L',
    coq.ltac.call "mypose_elpi" [trm (app [X | L'])] G [G'], 
    coq.ltac.open (mypose_list XS) G' GL.
  mypose_list [] _ _.


  pred applied_higher_order_or_polymorphic i:pair term (list term).
  applied_higher_order_or_polymorphic (pr X _) :-
    contains_prenex_ho_ty X,
    prenex_ho1_ty X.
  applied_higher_order_or_polymorphic (pr X _) :-
    polymorphic_ty X.


  solve (goal Ctx _ TyG _ _ as G) GL :-
    % `Trms` contains all the types of the hypotheses whose type is Prop
    ctx_to_hyps Ctx Trms,
    % `Na` containts all the eigenvariables, see
    %   https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/elpi-builtin.elpi#L393
    names Na,
    % `Subs` contains all the applications from `[TyG|Trms]` as a list of pairs
    %   of the function and its arguments
    subterms_list_and_args [TyG|Trms] Na Subs,
    coq.say "Subs = " Subs,
    % `L` is the sublist of `Subs` whose functions verify both
    %   `contains_prenex_ho_ty` and `prenex_ho1_ty`, that is to say functions
    %   whose type has the shape Π (A₁ ... Aₙ : Type). Π f: (Π x: B. C). ...
    %   where B is not a product itself (CK: not sure why)
    %   or are polymorphic
    std.filter Subs applied_higher_order_or_polymorphic L,
    coq.say "L = " L,
    % `L'` truncates the lists of arguments to keep only those of type `Type` or
    %   product: this is the list of terms that we want to give name to
    trm_and_args_type_funs L L',
    coq.say "L' = " L',
    % The remaining of the tactic poses them
    std.rev Ctx Ctx',
    add_pos_ctx_pr Ctx' L' L'',
    mypose_list L'' G GL.

}}.

From Stdlib Require Import List.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
List.map g (List.map f l) = map (fun x => g (f x)) l.
intros.
elpi applied_higher_order_and_polymorphic. Abort.

Tactic Notation "applied_higher_order_and_polymorphic" :=
  elpi applied_higher_order_and_polymorphic.

Import ListNotations.

Section Tests.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
applied_higher_order_and_polymorphic.
Abort.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros. 
assert (IHl : map g (map f l) = map (fun x : A => g (f x)) l) by admit.
 applied_higher_order_and_polymorphic. (* remove duplicates *)
Abort. 

Goal (
forall (A B C : Type)
(f : A -> B)
(g : B -> C),
let f0 := fun x : A => g (f x) in
((forall x : A, f0 x = g (f x)) ->
(forall (x : Type) (x0 x1 : x) (x2 x3 : list x),
     x0 :: x2 = x1 :: x3 -> x0 = x1 /\ x2 = x3) ->
(forall (x : Type) (x0 : x) (x1 : list x),
     [] = x0 :: x1) ->
map g (map f []) = map f0 [])).
Proof. intros. applied_higher_order_and_polymorphic. Abort.

Goal forall (A B:Type) (l:list A) (f:A -> B),
    map id (map f l) = map (fun x => id (f x)) l.
Proof.
  intros.
  applied_higher_order_and_polymorphic.
Abort.

End Tests.
