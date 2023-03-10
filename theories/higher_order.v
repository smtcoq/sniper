Require Import utilities.
Require Import expand.
Require Import elimination_fixpoints.
Require Import elimination_pattern_matching.

From elpi Require Import elpi.

Ltac mypose t := let Na := fresh "f" in pose t as Na; fold Na. (*TODO fold in all hyps except
the self refering one *)

(* TODO : use orchestrator instead of coding a small snipe here *)
Ltac mypose_and_reify_def t := let Na := fresh "f" in pose t as Na; fold Na ;
let H := fresh "H" in assert (H : Na = t) by reflexivity ; let hd := get_head t in 
unfold hd in H. (* expand_hyp_cont H ltac:(fun H' => 
eliminate_fix_ho H' ltac:(fun x => let T := type of x in idtac T)). *)

Elpi Tactic anonymous_funs.

Elpi Accumulate File "elpi/higher_order.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate lp:{{

  pred mypose_list i: list term, i: goal, o: list sealed-goal.
  mypose_list [X|XS] G GL :- coq.ltac.call "mypose" [trm X] G [G'],
    coq.ltac.open (mypose_list XS) G' GL.
  mypose_list [] _ _.

  solve (goal Ctx _ TyG _ _ as G) GL :- ctx_to_tys Ctx Trms,
    get_anonymous_funs_list [TyG|Trms] Lfun, mypose_list Lfun G GL.

}}.
Elpi Typecheck.

Require Import List.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
pose (h := (fun x => x + 1) 42 = 43). 
elpi anonymous_funs. Abort.

Elpi Tactic prenex_higher_order.
Elpi Accumulate File "elpi/higher_order.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate File "elpi/subterms.elpi".
Elpi Accumulate lp:{{

  pred mypose_list i: list (pair term (list instance)), i: goal, o: list sealed-goal.
  mypose_list [pr X L |XS] (goal Ctx _ _ _ _ as G) GL :- std.rev Ctx Ctx',
    std.map L (instance_to_term Ctx') L', 
    coq.ltac.call "mypose_and_reify_def" [trm (app [X | L'])] G [G'], 
    coq.ltac.open (mypose_list XS) G' GL.
  mypose_list [] _ _.


  solve (goal Ctx _ TyG _ _ as G) GL :- ctx_to_hyps Ctx Trms, names Na,
    subterms_list_and_args [TyG|Trms] Na Subs,
    std.filter Subs (x\ fst x X, contains_prenex_ho_ty X, prenex_ho1_ty X) L, trm_and_args_type_funs L L', std.rev Ctx Ctx', 
term_to_instance_pr Ctx' L' L'', mypose_list L'' G GL.

}}.
Elpi Typecheck.
Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
elpi anonymous_funs.
elpi prenex_higher_order. Abort.

Goal ((forall (x : nat) (a : nat) (l : list nat), 
@hd nat x (@cons nat a l) = match (@cons nat a l) with
| nil => x
| y :: xs => y
end)). elpi anonymous_funs. Abort. 
(* Bug fix : each branch of a match is a function so the function looking 
for anonymous functions were returning the branches and we do not want that.
So we stopped the recursive search when meeting a match.
But this should be improved by creating a special predicate for matches.  *)

Tactic Notation "anonymous_funs" :=
  elpi anonymous_funs.

Tactic Notation "prenex_higher_order" :=
  elpi prenex_higher_order.

From Ltac2 Require Import Ltac2.

(* new_hypothesis h h++h' returns h' *)
(* Note: code duplication with deciderel *)
Ltac2 rec new_hypothesis
(h1: (ident * constr option * constr) list) 
(h2 : (ident * constr option * constr) list) := 
match h1 with
| [] => h2
| x :: xs => match h2 with
        | [] => []
        | y :: ys => new_hypothesis xs ys
      end
end.


Ltac2 rec hyps_printer (h : (ident * constr option * constr) list) 
:=
match h with
| [] => ()
| x :: xs => match x with
            | (id, opt, cstr) => 
let () := Message.print (Message.concat (Message.of_ident id)
                                        (Message.concat (Message.of_string " : ")
                                                        (Message.of_constr cstr))) 
in hyps_printer xs
end 
end.

Ltac2 prenex_higher_order_with_equations (u : unit) :=
let h := Control.hyps () in 
let () := ltac1:(prenex_higher_order) in
let h' := Control.hyps () in 
let h0 := new_hypothesis h h' in 
let rec aux h :=
  match h with
  | [] => ()
  | x :: xs => match x with
            | (id, opt, cstr) => let hltac2 := Control.hyp id in
              let hltac1 := Ltac1.of_constr hltac2 in ltac1:(H |- let T := type of H in let U := type of T 
              in tryif (constr_eq U Prop) then expand_hyp_cont H ltac:(fun H' => 
              eliminate_fix_ho H' ltac:(fun H'' => eliminate_dependent_pattern_matching H''); clear H)
else idtac) hltac1 ; aux xs
            end
end 
in aux h0.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
ltac1:(anonymous_funs).
prenex_higher_order_with_equations (). Abort.

Tactic Notation "prenex_higher_order_with_equations" :=
ltac2:(prenex_higher_order_with_equations ()).
