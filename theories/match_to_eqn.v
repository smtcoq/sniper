From elpi Require Import elpi.

Elpi Tactic match_to_eqn.
Elpi Accumulate lp:{{

pred mkeqbo i:term, i:term, i:term, i:term, o:term.
mkeqbo {{ fun x => lp:(Bo x) }} K E M {{ fun x => lp:(Bo1 x) }} :- !,
  @pi-decl `x` _ x\
    mkeqbo (Bo x) {coq.mk-app K [x]} E M (Bo1 x).
mkeqbo B K E (match _ RTy Bs as M) {{ fun h : lp:E = lp:K => lp:Proof h : lp:Ty }} :-
  Proof = {{ @eq_ind_r _ lp:K lp:Pred (refl_equal lp:B) lp:E }},
  Pred = {{ fun x => lp:{{ match {{ x }} RTy Bs }} = lp:B }},
  Ty = {{ lp:M = lp:B }}.

pred mkeqn i:list term, i:list term, i:term, i:term, o:term.
mkeqn [] [] _ _ {{ _ }}.
mkeqn [B|Bs] [K|Ks] E M {{ let h := lp:Bo in lp:(R h) }} :-
  mkeqbo B K E M Bo,
  @pi-def `h` _ Bo h\
    mkeqn Bs Ks E M (R h).

solve (goal _ _ _ _ [trm (match E _ Bs as M)] as G) GL :- std.do! [
  std.assert-ok! (coq.typecheck M _) "illtyped input",
  coq.typecheck E Ty ok,
  coq.safe-dest-app Ty (global (indt I)) Args,
  coq.env.indt I _ _ Pno _ Ks _,
  std.take Pno Args Params,
  std.map Ks (x\r\ coq.mk-app (global (indc x)) Params r) KPs,
  mkeqn Bs KPs E M T,
  %BUG: coq.say "M=" M "T=" {coq.term->string T},
  std.assert! (refine T G GL) "bug in term generation",
].
}}.
Elpi Typecheck.




Lemma foo :  (match 2 with
| 0 => True
| S k => False
end).

elpi match_to_eqn (match 2 with
| 0 => true
| S k => false
end). clearbody h0. clearbody h.
rewrite h0.
