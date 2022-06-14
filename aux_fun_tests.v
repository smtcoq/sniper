

(*** Metavariables conventions ***)
(* indu : inductive  (the 1st argument of the constructor tInd )*)
(* mind: mutual_inductive_body *)
(* ooind : one_inductive_body *)
(* p : number of parameters of an inductive *)
(* roind : rank of an oind in a mind/rank of a projection *) 
(* noind : number of oind's in a mind *) (* no *)
(* nc : number of constructors of a oind *) (* k *)
(* k : rank of a constructor in a oind *)    (* i *)
(* n : number of arguments of a constructor *)
(* j : rank of an argument of a constructor *)
(* j: rank of case in a pattern-matching (constructor tCase): starts from 1 *)
(* REMPLACER : cela devrait être nc*)   

Require Import utilities. 
Require Import interpretation_algebraic_types.
Require Import elimination_polymorphism.
Require Import case_analysis.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.

(* function to comment :  pose_inductive_tac *)

Open Scope string_scope.  

Import ListNotations MonadNotation. 




(* reified term selectors in lists and lists of lists *)
Definition sel_lterm (i : nat) (l : list term) := nth i l impossible_term_reif.

Definition sel_llterm (k : nat) (i : nat) (l : list (list term)) := 
  sel_lterm i (nth k l []).

Inductive nelist {A : Type} : Type :=
	sing :  A -> nelist    | necons : A -> nelist -> nelist .
      
Inductive biclist {A B : Type} : Type :=
(*  sing1 : A -> biclist  
  | sing2 : B -> biclist *)
  | bicnil : biclist
  | cons1 : A -> biclist -> biclist
  | cons2 : B -> biclist -> biclist. 



(*

Ltac proj k n x :=
   let k0 := n - k 
   match k with
   | 0 => match 

let x := fresh in pose constr:(k - 1) constr:(n -1) 
*)


Definition get_ind_ident (kerna : kername) := let (mdp , idind) := kerna in idind.





MetaCoq Quote Definition Type_reif := Eval hnf in Type.
MetaCoq Quote Definition Prop_reif := Eval hnf in Prop.
MetaCoq Quote Definition Set_reif := Eval hnf in Set.
MetaCoq Quote Definition eq_reif := Eval hnf in @eq. 

MetaCoq Quote Definition nat_reif := nat.
MetaCoq Quote Recursively Definition nat_env_reif := nat.



Definition list_nat := @list nat.
MetaCoq Quote Definition list_nat_reif :=  (@list nat).
MetaCoq Quote Recursively Definition list_nat_env_reif := list_nat.             
MetaCoq Quote Definition cons_nat_type_reif := (nat -> list_nat -> list_nat).
MetaCoq Quote Definition nil_type_reif := (forall (A : Type), list A).
(* \Q nil_type_reif and cons_nat_reif do not work because do not
currently have  the right universes levels *)


MetaCoq Quote Definition cons_reif := cons.
MetaCoq Quote Definition sing_reif := sing.
MetaCoq Quote Definition necons_reif := necons.


MetaCoq Quote Definition bicnil_reif := bicnil.
MetaCoq Quote Definition cons1_reif := cons1.
MetaCoq Quote Definition cons2_reif := cons2.





MetaCoq Quote Definition zero_reif := 0.
MetaCoq Quote Definition one_reif := 1.
MetaCoq Quote Definition two_reif := 2.


MetaCoq Quote Definition nil_nat_reif := Eval cbn in (@nil nat).
MetaCoq Quote Definition list_one_two_reif := Eval cbn in [1 ; 2].
MetaCoq Quote Definition list_one_two_two_reif := Eval cbn in [1 ; 2 ; 2].

MetaCoq Quote Definition list_one_two_two_reif' := (List.app [1] [2 ; 2]).



(** Reified objects functions *)
 
Definition cons_nat := @cons nat.



MetaCoq Quote Definition length_reif := @List.length.
MetaCoq Quote Definition le_reif := le.
MetaCoq Quote Definition S_reif := Eval cbn in S.
MetaCoq Quote Recursively Definition S_env_reif := S.

Print S_reif. 
Print S_env_reif.

MetaCoq Quote Definition O_reif := O.
MetaCoq Quote Definition add_reif := Eval cbn in Nat.add.
MetaCoq Quote Definition nil_reif := nil.
MetaCoq Quote Recursively Definition nil_env_reif := nil.
MetaCoq Quote Recursively Definition cons_env_reif := cons.
MetaCoq Quote Recursively Definition cons_nat_env_reif := cons_nat.
MetaCoq Quote Definition cons_nat_reif := cons_nat.
MetaCoq Quote Definition list_reif := @list.
MetaCoq Quote Recursively Definition list_env_reif := @list.

MetaCoq Quote Definition nelist_reif := @nelist.
MetaCoq Quote Recursively Definition nelist_env_reif := @nelist.

MetaCoq Quote Definition biclist_reif := @biclist.

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

MetaCoq Quote Definition even_reif := even.
MetaCoq Quote Definition odd_reif := odd.




MetaCoq Quote Definition cons_typ_reif := (forall (A: Type), A -> list A -> list A).

Print list_env_reif.

Definition nat_indu := ltac:(let s := fresh in  pose_inductive_tac nat s ; exact s).
Definition list_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).
Definition list_nat_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).


(* \TODO eliminate the "let in" which currently appear in list_mind *)
Definition nat_mind :=  ltac:(let x := fresh in pose_mind_tac nat x ; cbn in x ; exact x).
Definition list_mind :=  ltac:(let x := fresh in pose_mind_tac list x ; cbn in x ; exact x).
Definition nelist_mind :=  ltac:(let x := fresh in pose_mind_tac @nelist x ; cbn in x ; exact x).
Definition biclist_mind :=  ltac:(let x := fresh in pose_mind_tac @biclist x ; cbn in x ; exact x).
Print biclist_mind.


MetaCoq Quote Definition bclist_reif := biclist.

Goal False.
Print bclist_reif.

let x := constr:(cutEvar bclist_reif) in pose x as kik ; compute in kik.
Abort.

Goal False.
let x:= constr:(get_params_from_mind biclist_mind) in pose x as biclist_params ; compute in biclist_params.
Abort.


Definition nat_oind := {|
ind_name := "nat"%string;
ind_type := tSort (Universe.of_levels (inr Level.lSet));
ind_kelim := IntoAny;
ind_ctors := [("O"%string, tRel 0, 0);
             ("S"%string,
             tProd
               {|
               binder_name := nAnon;
               binder_relevance := Relevant |}
               (tRel 0) (tRel 1), 1)];
ind_projs := [];
ind_relevance := Relevant |}.




Ltac pose_oind_tac t i idn := let s := fresh "s" in pose_mind_tac t s ; pose (nth i s.(ind_bodies)  nat_oind) as idn; simpl in idn ; clear s.
(* pose_oind take an (unreified) inductive  I and outputs the i-th one_inductive_block of I *) 
(* when I is not a mutual inductive, i should be equal to 0 *)
(* the tactic uses nat_oind as the defaut value for nth *)

Definition list_oind := ltac:(let s := fresh in pose_oind_tac list 0 s ; compute in s ; exact s).


(* pose_list_ctor_oind t i idn computes the lists of types of the constructors of i-th one inductive block of t and poses it as idn.
   Then, idn has type list term
*)
Ltac pose_list_ctor_oind t i idn := let x := fresh  in  pose_oind_tac t i x ; let lctor := constr:(list_ctor_oind x) in pose lctor as idn ; compute in idn ; clear x.

Goal False.
pose_list_ctor_oind list 0 kik.
clear.
pose_list_ctor_oind even 0 evenctor.
pose_list_ctor_oind even 1 oddctor.
let x := constr:(debruijn0 list_indu 2) in pose x as kik ; unfold debruijn0 in kik ; unfold utilities.switch_inductive in kik ; simpl in kik.

Abort.

(*testing get_ctors_and_types *)
Goal False. 
let x := constr:(get_ctors_and_types_i list_indu 1 1 0 [] list_oind) in pose x as gttlist ; compute in gttlist.
Abort.

(* \TMP
Definition get_ctors_and_types_i (indu : inductive) (p :nat) (n: nat) (i : nat) (u : Instance.t) (oind : one_inductive_body ) *)
             
Goal False. 
let x := constr:(hd (list_mind.(ind_bodies))) in pose x as kik ; compute in kik.
Abort.

Ltac kooooo t na :=
   constr:((4,5)).



(***********************************)

(***** tests Pierre  (à transférer)      *********)

(***********************************)

(* i : numéro de la projection *)
(* exemple: cons est le 2ème constructeur de list 
 - pour elim_{1,0}, i est 0, ty_default est nat et pour elim_{1,1}, c'est 1 et list nat 
- nb_construct 2 ou 1.
- total_arg c'est 2 ou 3 (compte-t-on les paramètres ?)
*)
(* ty_default *)



Goal False.
let x := constr:(bind_def_val_in_gen [[tRel 0 ] ; [tRel 0 ; tApp list_reif [tRel 0] ; tApp list_reif [tRel 0]]; [tRel 0 ; tApp nat_reif [tRel 1]]  ] [1 ; 3 ; 2]) in pose x as kik ; compute in kik.
Abort.
(* list_args := val compute in (split (list_args0)).1   *)



(**** Old info function. To sort *)


Ltac pose_quote_term c idn :=
  let X :=  c in  quote_term X ltac:(fun Xast => pose Xast as idn).


Ltac get_ind_param t idn := 
    let tq := fresh "t_q" in pose_quote_term t tq ;
    lazymatch eval hnf in tq with
     | tInd ?indu ?u =>  pose (indu,u) as idn  ; clear tq
     end.




(**** Before producing the projections *)
 

Goal False. (* \TMP *)
let x := constr:(mkCase_list_param [2 ; 3 ; 1] 2 2) in pose x as mklistparamex ; compute in mklistparamex.
Abort.




(******* Producing the projections *)

Goal False.
(* \TODO commenter les exemples*)
let x := constr:(proj_ij 0 [] nat_reif nat_indu 1 0 [[]; [tRel 0]] [0 ; 1]
(nat_reif)) in pose x as pS_reif ; compute in pS_reif.
pose_unquote_term_hnf pS_reif pS.
clear.
let x := constr:(proj_ij 1 [Set_reif] list_reif list_indu 1 1 [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2]
(tApp list_reif [tRel 0])) in pose x as proj_list11_reif ; compute in proj_list11_reif.
pose_unquote_term_hnf proj_list11_reif proj_list_11.
let x := constr:(proj_ij 1 [Set_reif] list_reif list_indu 1 0 [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2]
(tRel 0)) in pose x as proj_list10_reif ; compute in proj_list10_reif.
pose_unquote_term_hnf proj_list10_reif proj_list_10. clear -proj_list_10 proj_list_11.
Abort.


Goal False. 
let x := constr:(collect_projs 1 [Set_reif] list_reif list_indu [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2] 2) in pose x as list_projs ; compute in list_projs. 

let x := constr:(sel_llterm 1 0 list_projs)  
in pose x as p10_reif ; compute in p10_reif.
pose_unquote_term_hnf p10_reif p10.
let x := constr:(sel_llterm 1 1 list_projs) in pose x as p11_reif ; compute in p11_reif.
pose_unquote_term_hnf p11_reif p11.
Abort.






Goal False. 
let x := declare_projs_ctor_i na 1  [Set_reif]   list_reif list_indu [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2]  1 [tRel 0 ; tApp list_reif [tRel 0]] 2 in pose x as tVars_list ;  compute in tVars_list .
pose_unquote_term_hnf (sel_lterm 0 tVars_list) p10_reif.
pose_unquote_term_hnf (sel_lterm 1 tVars_list) p11_reif.
Abort.


Goal False.
let x := declare_projs list  1 [Set_reif] list_reif list_indu [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2] 2 in pose  x as tVars_list.
Abort.


Ltac declare_projs1 na p lA_rev  I  indu llAunlift  ln nc 
:= idtac "debut" ; 
let llAu_rev := constr:(tr_rev llAunlift) in let ln_rev := 
constr:(tr_rev ln) in idtac "let rec aux1" ; 
 let rec aux1 k  i  lAk' acc := 
 idtac "blut 0";  let x := constr:((i,lAk'))   in (* idtac "kikoo" ; *)
  match eval hnf in x with
   | (?i,?lAk') => match eval hnf in i with
     | 0 => constr:(acc) 
     | S ?i => match eval hnf in lAk' with
       | ?Akiu :: ?lAk' => idtac "res1" ; let pki := constr:(proj_ij p lA_rev I indu k i llAunlift ln (Akiu)) in 
       let name :=  fresh "proj_" na in let _ := match goal with _ => pose (name := pki ) end  in let y := metacoq_get_value (tmQuote name)  in let acc0 := constr:(y :: acc) in let res1 := aux1 k i lAk'  acc0 in constr:(res1)
       end end
   (* | _ => idtac "error declare_projs 1" *)
  end 
  in 
 let rec aux2 llAu' ln' k  acc :=
let y := constr:(((k,llAu'),ln')) 
in (* idtac "loool" ;*) match eval hnf in y with
| (?y0 , ?ln0') => (* idtac "blut 1" ; *)
  match eval cbv in ln0' with
  | (@nil nat) =>  (* idtac "blut 3 0" ; *) constr:(acc) 
  | ?i :: ?ln1' => (*  idtac "blut 3" ;*)
    match eval hnf in y0 with 
    | (?k, ?lAu') => lazymatch eval hnf in k with
      | S ?k => (* idtac "blut 5" ; *) match eval hnf in lAu' with
        | ?lAk :: ?lAu'=> let res2 := aux2 llAu' ln' k constr:((aux1 k i (tr_rev lAk) (@nil term)) :: acc) in constr:(res2)
  end 
  end   
  end
  end 
  (* |_ => idtac "error declare_projs 1" *)
end
in 
let res := aux2 llAu_rev ln_rev nc (@nil term)  in constr:(res)
. 


Goal False.
let x := declare_projs list  1 [Set_reif] list_reif list_indu [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2] 2 in pose x as dp_list.
Abort.

(**** producing the generation statement *)




Goal false.
let x := constr:(get_eq_x_ctor_projs 3 (S_reif) [tRel 0; tRel 25; tRel 49] 
8) in pose x as gexcpex ; compute in gexcpex.
Abort.


Goal False.
let x:= constr:(get_generation_disjunction 3 nat_reif  100 [S_reif ; O_reif ; O_reif ]
  [[tRel 13 ; tRel 15 ; tRel 8] ; [tRel 33 ; tRel 45] ; [tRel 60 ; tRel 70 ; tRel 72]] [3 ; 2 ; 3]) in pose x as ggdex ; compute in ggdex.  clear.
Abort.

Goal False.
let x := constr:(args_of_projs_in_disj [3 ; 8 ; 2]) in pose x as kik ; compute in kik.
Abort.
  
Goal False.
Proof.
pose (2,3) as x. pose x.1 as y. Eval compute in y.
Abort.





Goal False. (* \TMP *)
let x := kooooo list blut in pose x as kik.
Abort.




Goal False. 

pose_gen_statement list. 
pose_gen_statement @nat.
pose_gen_statement @biclist.
pose_quote_term (fun (A : Type) (x x0 : list A) =>
match x0 with
| [] => x
| _ :: x1 => x1
end ) pl1.
pose_quote_term (fun (A : Type) (x : A) (x0 : list A) =>
match x0 with
| [] => x
| x1 :: _ => x1
end ) pl0.
Abort.


Goal False.
 pose_quote_term
(fun (l : list nat) => match l with
| [] => 0
| x  :: l0 => x end
  ) p1.
  pose_quote_term
  (fun (l : @biclist nat bool) => match l with
  | bicnil => 0
  | cons1 x l0 => x 
  | cons2 _ _ => 1 end 
    ) p2.
clear.
pose_quote_term (fun (A : Type)  ( l : @nelist A)  => match l with
| sing a => a 
| necons  x l0 => x 
end
  ) p3.
Abort.

Goal False.
pose_gen_statement  list. 
pose_gen_statement  nat.
pose_quote_term  (forall (A : Type) (d : A) (d0 x : list A), x = [] \/ x = proj_list0 A d x :: proj_list A d0 x) gen_stat_reif. 
pose_quote_term (fun (A : Type) (x x0 : list A) => match x0 with
| [] => x
| _ :: x1 => x1
end ) pl1.
pose_quote_term (fun (A : Type) (x : A) (x0 : list A) => match x0 with
| [] => x
| x1 :: _ => x1
end ) pl0.
pose_quote_term (fun x x0 : nat => match x0 with
| 0 => x
| S x1 => x1
end ) pn0.
Abort.


(***********************************************)
(* Tests on utilities.v                        *)
(***********************************************)


Goal False.
let x := constr:(mkProd_rec [tRel 3 ; tRel 5 ; tRel 8] (tRel 13)) in pose x as mprex ; compute in mprex.
Abort.


Goal False. 
info_indu nat nat_info_indu.
info_indu list list_info_indu.
Abort.


Goal False.
let x := constr:(Rel_list 8 4) in pose x as kik ; compute in kik.
Abort.





(***********************************************)
(* Tests on interpretation_algebraic_types.v   *)
(***********************************************)

Goal False.
info_indu nat natoblut.
info_indu list listoblut.
Abort.



Goal False.
let x := constr:(is_inj (tApp list_reif [tRel 2]) cons_reif [tRel 0 ; tApp list_reif [tRel 1]] 1 ) in pose x as is_inj_cons ; compute in is_inj_cons.
Abort.



Goal forall (n m k: nat), exists (x y z: nat), x = n /\ y = m /\ z = k .
Proof. intros_exist_aux  3 ltac:(idtac).  let x := fresh "x" in let x:= fresh "x" in idtac. repeat split.
Abort.

(***********************************************)
(* Tests on eliminators.v                      *)
(***********************************************)

(* meaning of the metavariables *)
(* nbproj : rank of a projection e.g. *)
(* exemple: cons est le 2ème constructeur de list 
 - pour elim_{1,0}, nbproj est 0, ty_default est nat et pour elim_{1,1}, c'est 1 et list nat 
- nb_construct 2 ou 1.
- total_arg c'est 2 ou 3 (compte-t-on les paramètres ?)
*)


(* _app : the inductive applied to its possible de Bruijn indices
* nat_app = nat_reif
* list_app = list_reif [Rel 0]
* nelist_app = nelist_reif [Rel0]
*)


(* _total_args or _tot_args is equal to the total number of parameters of the constructors:
   is equal to 1 for nat
   is equal to 2 for list, 
   is equal to 3 for nelist
*)

(* _lpars :
 nat_lpars = []
 list_lpars = [Rel 3]
 nelist_pars = [Rel 4]
*)

(* list_args := (split list_args_len).1 :
* nat_list_args = [ [] ; nat_reif ]
* list_list_args = [ [] ; [Rel 0 ; list_reif [Rel 0]]]
* nelist_list_args =  [ [Rel 0] ; [Rel 0 ; nelist_reif [Rel 0] ] ]
*)

(* list_ty 
* nat_list_ty = [nat_reif ; Prod _ nat_reif nat_reif]
* list_list_ty = [ tProd "A" Set_reif. list_reif [Rel 0] ;
   tProd "A" Set_reif. tProd _ (Rel 0). tProd _ (list_reif [Rel 1]). list_reif Rel 2  ]
* nelist_list_ty = [ tProd "A" Set_reif. tProd _ (Rel 0). nelist_reif [Rel 1] ; 
   tProd "A" Set_reif. tProd _ (Rel 0). tProd _ (nelist_reif [Rel 1]). nelist_reif Rel 2  ]
   *)

(* list_pars 
* nat_list_pars = []
* list_list_pars = [Set_reif]
* nelist_list_pars = [Set_reif].
*)

(* npars
nat_npars = 0
list_npars = 1
nelist_npars =
*)

Goal False.
split_info1 nat "nat". clear.
split_info1 list "list".  (* the second arg seems useless*)
clear. split_info1 @nelist  "nelist".
Abort.


Goal False.
split_info1 list "list". 
Print get_nbproj_nbargprevcons.
let res :=  (get_nbproj_nbargprevcons n I list_ty_pars list_app list_indu list_npars list_list_args list_tot_args list_lpars list_constructors_reif nb (@nil term)) in pose res as blut. Eval compute in blut.


Ltac get_nbproj_nbargprevcons n I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb list_eq :=
match n with
Abort.


Ltac get_nbproj_nbargprevcons n I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb list_eq :=


(**** eliminators.v ****)

Goal False.

Print nil_type_reif.
pose (tProd
  (mkNamed "A")
  (tSort
     (Universe.of_levels
        (inr
           (Level.Level
              "Sniper.aux_fun_tests.465"))))
  (tApp
    list_reif [tRel 0]))
as blut0.
pose (tProd
  (mkNamed "A")
  (tSort
     (Universe.of_levels
        (inr
           (Level.Level
              "Sniper.aux_fun_tests.387"))))
  (tProd
     {|
       binder_name := nAnon;
       binder_relevance := Relevant
     |} (tRel 0)
     (tProd
        {|
          binder_name := nAnon;
          binder_relevance := Relevant
        |}
        (tApp
           list_reif [tRel 1])
        (tApp list_reif [tRel 2])))) as blut1.
(* let list_info := fresh "list_info" in get_info_quote list list_info. *)
(* let '(list_indu, list_I_app, list_lpars, list_total_args, list_lists_args, list_list_ty, list_ty_pars, list_npars) := ????? *)



split_info1 list "list".

get_list_args_len_quote list list_lal.
get_ty_arg_constr list list_tarc.

pose ((tApp (* en mettant un idtac dans eliminators.v *)
   (tInd
      {|
        inductive_mind :=
          (MPfile
             ["Datatypes"; "Init";
             "Coq"], "list");
        inductive_ind := 0
      |} []) [tRel 0])) as list_ty_default.
(* on aussi tRel 0 qui doit correspondent à un autre ty_default *)

(* pour ty_default avec un idtac *)



pose (tLambda
   {|
     binder_name := nNamed "x";
     binder_relevance := Relevant
   |}
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 2])
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 3])) as rtyp1. 
pose 
(tLambda
   {|
     binder_name := nNamed "x";
     binder_relevance := Relevant
   |}
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 2]) 
   (tRel 3)) as rtyp0.


(* proj_one_constructor_default_var (i : term) (ty_default : term)
 (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) *) 
clear list_info.
let x := constr:(proj_one_constructor_default_var  (tApp list_reif [tRel 0]) 
 (tApp list_reif [tRel 0])  
list_indu 1 0 1 list_tarc rtyp1)
in pose x as y; compute in y.
Print tCase.
pose_unquote_term_hnf y projtruc.
Abort.
