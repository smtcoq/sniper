From elpi Require Import elpi.

Elpi Tactic instantiate_param_strategy.
Elpi Accumulate File "utilities.elpi".
Elpi Accumulate File "construct_cuts.elpi".
Elpi Accumulate File "instantiate.elpi".
Elpi Accumulate lp:{{
  
    pred inst_param_str i: list term, i: list term.
      inst_param_str [X | L1] L2 L3 :- 
        instances_param_indu_strategy X L2 L4, assert_list_with_hyp X L4, 
        inst_param_str L1 L2.
     inst_param_str [] []. 

(* TODO : add the default instances + write assert_list_hyp *)

    solve (goal Ctx _ Ty _ L as G) GL :- 
      collect_polymorphic_hypothesis_from_context Ctx L',
      

}}.