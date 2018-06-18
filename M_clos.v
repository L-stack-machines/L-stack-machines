From LM Require Import Prelims Refinements L Programs Closures M_stack.

(** * Closure Machine *)

Definition stateC : Type := list Clo*list Clo.
Hint Transparent stateC.

Reserved Notation "σ ≻C_ l σ'" (at level 70, l at level 0,format "σ  '≻C_' l  σ'").

Inductive stepC : label -> stateC -> stateC -> Prop:=
| step_nil E T V:
    (retT/E::T,V) ≻C_τ (T,V)
| step_load P E x V p T:
    E.[x] = Some p ->
    ((varT x P)/E::T,V) ≻C_τ (P/E::T,p::V)
| step_pushVal P Q E T V:
    ((lamT Q P)/E ::T,V)  ≻C_τ (P/E::T,Q/E::V)
| step_betaC P E T e Q F V:
    ((appT P)/E :: T,e :: Q/F ::V) ≻C_β (Q/(e::F) :: P/E :: T,V)
where "σ  ≻C_ l  σ'" := (stepC l σ σ').

Notation "(≻C_ l )" := (stepC l) (at level 0, format "'(≻C_' l ')'").
(* workaround to prefere "x ≻ y" over "(≻) x y"*) Notation "σ ≻C_ l σ'" := 0.
Notation "σ ≻C_ l σ'" := (stepC l σ σ').
Notation "(≻C)" := (any stepC) (at level 0).

Notation "σ ≻C σ'" := (any stepC σ σ') (at level 70).

Canonical Structure clos_machine := {| M_rel := stepC |}.

Hint Constructors stepC.

Definition closedSC : stateC -> Prop :=
  fun '(T,V) => Forall (<C 0) T /\ Forall (<C 1) V.

Definition repsCS (π:stateC) (σ:stateS) : Prop :=
  let '(T,V):= π in closedSC (T,V) /\ (map (δC 0) T,map (δC 1) V) = σ.
Notation "(≫CS)" := (repsCS) (at level 0).
Notation "π ≫CS σ" := (repsCS π σ) (at level 70). 

Lemma repsCS_functional :
  functional (≫CS).
Proof.
  intros [] ? ? [? <-] [? <-]. tauto.
Qed.

Local Lemma cbound_cons P e E :
  P/E <C 1 -> e <C 1 -> P/(e::E) <C 0.
Proof.
  inversion 1. constructor;cbn;intuition (subst;eauto).
Qed.


Lemma reducibility T V:
  reducible (≻S) (map (δC 0) T,map (δC 1) V) -> reducible (≻C) (T,V).
Proof.
  intros (σ'&l'&R). unfold reducible.
  destruct T as [|[[] E]];cbn in R. 
  -now inv R.
  -eauto.
  -cbn in R. destruct _ eqn:eq. 2:now inv R.
   rewrite <-minus_n_O in eq. apply nth_error_map in eq as (?&?&?). eauto.
  -destruct V as [|? [|[]]]. 3:eauto.
   all:cbn in R. all:inv R.
  -eauto.
Qed.


Ltac inv_closed_clos :=
  repeat
    match goal with
    | [H:closedSC (_,_) |- _] => inv H
    | [H:Forall _ (_::_) |- _] => inv H
    | [H:_/_ <C _|- _] => inv H
    | [H:lamT _ _ <P _  |- _] => inv H
    | [H:varT _ _<P _  |- _] => inv H
    | [H:appT _<P _  |- _] => inv H
    end.

Lemma closedSC_preserved T V T' V' :
  closedSC (T,V) -> (T,V) ≻C (T',V') -> closedSC (T',V').
Proof.
  intros ? [l R]. inv R.
  all:inv_closed_clos.
  all:split;repeat apply Forall_cons.
  all:eauto using nth_error_In, cbound_cons.
Qed.

Lemma tau_simulation T V T' V':
  (T,V) ≻C_τ (T',V') -> (map (δC 0) T,map (δC 1) V) ≻S_τ (map (δC 0) T',map (δC 1) V').
Proof.
  intros H. inv H. all:cbn. 
  2:erewrite <-minus_n_O, map_nth_error.
  all:eauto.
Qed.

Lemma beta_simulation T V T' V':
  closedSC (T,V) -> (T,V) ≻C_β (T',V') -> (map (δC 0) T,map (δC 1) V) ≻S_β (map (δC 0) T',map (δC 1) V').
Proof.
  intros cs H. inv H. cbn.  
  rewrite substPl_cons.
  -constructor.
  -inv_closed_clos. eapply Forall_map,Forall_forall. auto using translateC_boundP.
Qed.


Lemma clos_stack_refinement :
  refinement_M (≫CS).
Proof.
  split;cbn. 
  -intros [] [] [? [= <- <-]]. apply reducibility.
  -split.
   all:unfold repsCS.
   all:intros [T V] [T' V'] [T0 V0] [cs [= <- <-]] ?.
   all:specialize closedSC_preserved with (1:=cs) as ?.
   all:eauto 20 using tau_simulation,beta_simulation. 
Qed.

Lemma compile_clos_stack P:
  closedP P ->
  ([P/[]],[]) ≫CS ([P],[]).
Proof.
  intros cs. split.
  -unfold closedSC. eauto. 
  -cbn. now rewrite substPl_nil. 
Qed.

Definition repsCL:= rcomp repsCS repsSL. 
Notation "(≫CL)" := (repsCL) (at level 0).
Notation "π ≫CL s" := (repsCL π s) (at level 70).
(*
Lemma repsCL_equiv T V s:
  (T,V) ≫CL s <-> closedL s /\ exists A, δV (map (δC 1) V) = Some A /\ δT (map (δC 0) T) A = Some [s].
Proof.
  unfold repsCL,repsCS,repsSL. split.
  -intros (?&[? <-]&(A&?&?)). split. 2:eauto. admit.
  -intros (?&(A&?&?)). eexists;split. split. 2:reflexivity. 2:now cbn;eauto. admit. 
Abort. *)

Lemma clos_L_refinement :
  refinement_ARS (≫CL).
Proof.
  apply (composition clos_stack_refinement stack_L_refinement).
Qed.


Lemma compile_clos_L s:
  closedL s ->
  ([γ s retT/[]],[]) ≫CL s.
Proof.
  intros ?. eexists;split. 
  -apply compile_clos_stack. eauto using bound_compile.
  -apply compile_stack_L.
Qed.

