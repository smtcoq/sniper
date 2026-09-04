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

Elpi Tactic prenex_higher_order.

From Sniper.elpi Extra Dependency "higher_order.elpi" as HigherOrder.
From Sniper.elpi Extra Dependency "utilities.elpi" as Utils.
From Sniper.elpi Extra Dependency "subterms.elpi" as Subterms.
Elpi Accumulate File Utils.
Elpi Accumulate File Subterms.
Elpi Accumulate File HigherOrder.

Elpi Accumulate lp:{{

  pred mypose_list i: list (pair term (list term)), i: goal, o: list sealed-goal.
  mypose_list [pr X L |XS] (goal Ctx _ _ _ _ as G) GL :- 
    std.rev Ctx Ctx',
    std.map L (elim_pos_ctx Ctx') L',
    coq.ltac.call "mypose_elpi" [trm (app [X | L'])] G [G'], 
    coq.ltac.open (mypose_list XS) G' GL.
  mypose_list [] _ _.


  pred section_variable2hyp i:constant, o:term.
  section_variable2hyp C H :-
    GR = const C,
    coq.env.typeof GR Ty,
    coq.typecheck Ty {{ Prop }} ok,
    coq.env.global GR H.

  pred section_variables2hyps i:list constant, o:list term.
  section_variables2hyps [] [].
  section_variables2hyps [C|CS] [H|HS] :-
    section_variable2hyp C H,
    section_variables2hyps CS HS.
  section_variables2hyps [C|CS] HS :- section_variables2hyps CS HS.


  solve (goal Ctx _ TyG _ _ as G) GL :-
    % Collect the section variables
    coq.env.section-variables SV,
    % Collect hypotheses from the section variables
    section_variables2hyps SV SVHyps,
    % Collect hypotheses from the context
    ctx_to_hyps Ctx CtxHyps,
    % `Trms` contains all the types of the hypotheses (from the local context
    %   and the section variables) whose type is Prop
    std.append SVHyps CtxHyps Trms,
    % `Na` containts all the eigenvariables, see
    %   https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/elpi-builtin.elpi#L393
    names Na,
    % `Subs` contains all the applications from `[TyG|Trms]` as a list of pairs
    %   of the function and its arguments
    subterms_list_and_args [TyG|Trms] Na Subs,
    % `L` is the sublist of `Subs` whose functions verify both
    %   `contains_prenex_ho_ty` and `prenex_ho1_ty`, that is to say functions
    %   whose type has the shape Π (A₁ ... Aₙ : Type). Π f: (Π x: B. C). ...
    %   where B is not a product itself (CK: not sure why)
    std.filter Subs (x\ fst x X, contains_prenex_ho_ty X, prenex_ho1_ty X) L,
    % `L'` truncates the lists of arguments to keep only those of type `Type` or
    %   product: this is the list of terms that we want to give name to
    trm_and_args_type_funs L L',
    % The remaining of the tactic poses them
    std.rev Ctx Ctx',
    add_pos_ctx_pr Ctx' L' L'',
    mypose_list L'' G GL.

}}.

From Stdlib Require Import List.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
List.map g (List.map f l) = map (fun x => g (f x)) l.
intros.
elpi prenex_higher_order. Abort.

Tactic Notation "prenex_higher_order" :=
  elpi prenex_higher_order.

Import ListNotations.

Section Tests.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
prenex_higher_order.
Abort.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros. 
assert (IHl : map g (map f l) = map (fun x : A => g (f x)) l) by admit.
 prenex_higher_order. (* remove duplicates *)
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
Proof. intros. prenex_higher_order. Abort.

Section Max.
  Definition max {A} (cmp:A -> A -> comparison) (a b:A) :=
    match cmp a b with
    | Gt => a
    | _ => b
    end.

  Variable option_cmp : forall {A}, (A -> A -> comparison) -> option A -> option A -> comparison.
  Variable A : Type.
  Variable cmp : A -> A -> comparison.
  Hypothesis max_Some_Some : forall a b : A, max (option_cmp cmp) (Some a) (Some b) = Some (max cmp a b).

  Goal True.
  Proof.
    prenex_higher_order.
  Abort.
End Max.

End Tests.
