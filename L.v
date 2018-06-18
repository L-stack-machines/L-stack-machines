Require Import Prelims.


(** * Call-by-value Lambda Calculus *)

Inductive term : Type :=
| var (n : nat) : term
| app (s : term) (t : term) : term
| lam (s : term).

Coercion app : term >-> Funclass. 
Coercion var : nat >-> term .

Notation "(λ  s )" := (lam s) (right associativity, at level 0).

Inductive abstraction : term -> Prop := isAbstraction s : abstraction (lam s).
Hint Constructors abstraction.

Instance term_eq_dec : eq_dec term.
Proof.
  intros s t; unfold dec; repeat decide equality.
Defined.

(** ** Substitution *)

Fixpoint subst (s : term) (k : nat) (u : term) :=
  match s with
      | var n => if Dec (n = k) then u else (var n)
      | app s t => app (subst s k u) (subst t k u)
      | lam s => lam (subst s (S k) u)
  end.

(** ** Reduction *)

Reserved Notation "s  '≻L'  t" (at level 70). 
Inductive stepL : term -> term -> Prop :=
| stepLApp  s t     : app (lam s) (lam t) ≻L subst s 0 (lam t)
| stepLAppR s t  t' : t ≻L t' -> app (lam s) t ≻L app (lam s) t'
| stepLAppL s s' t  : s ≻L s' -> app s t ≻L app s' t
where "s  '≻L'  t" := (stepL s t).
Notation "(≻L)" := stepL (at level 0).
(* workaround to prefere "x ≻ y" over "(≻) x y"*) Notation "s  '≻L'  t" := 0.
Notation "s  '≻L'  t" := (stepL s t).

Canonical Structure L_ARS := {| ARS_X := term ; ARS_R := stepL |}.


Hint Constructors stepL.

Ltac inv_stepL :=
  repeat
    match goal with
    | H : _ _ ≻L _ |- _ => inv H
    | H : lam _ |- _ => inv H
    end.

Lemma stepL_funct :
  functional (≻L).
Proof.
  intros s t t' R1 R2. induction R1 in R2,t' |-*. 
  all: inv_stepL. all:repeat f_equal. all:eauto.  
Qed.

Fixpoint redL s : option term :=
  match s with
  |  app (lam s) (lam t) => Some (subst s 0 (lam t))
  |  app (lam s) t => try t':= redL t in Some ((lam s) t')
  |  app s t => try s':= redL s in Some (s' t)
  | _ => None
  end.

Lemma stepL_computable :
  stepFunction (≻L) redL.
Proof.
  intros s. induction s. 
  1,3:now cbn;intros ? R;inv R.
  cbn. destruct s1.
  -cbn. intros ? R. now inv R.
  -destruct redL. now eauto. intros ? R. inv R. eapply IHs1. eauto.
  -destruct s2 as [|s21 s22 |].
   +cbn. intros ? R. now inv R. 
   +destruct (redL (s21 s22)). now eauto. intros ? R. inv R. 2:easy. eapply IHs2. eauto. 
   +eauto. 
Qed.

(** ** Bound and Closedness for Terms *)
Reserved Notation "s <L k" (at level 70).

Inductive boundL : term -> nat -> Prop :=
  | bndvar k n : n < k -> var n <L k
  | bndApp k s t : s <L k -> t <L k -> s t <L k
  | bndlam k s : s <L S k -> lam s <L k
where "s <L k" := (boundL s k).
Hint Constructors boundL.

Definition closedL s:= boundL s 0 .

Hint Unfold closedL.


(** ** Stuck Terms *)

Inductive stuck: term -> Prop :=
  stuckVar x : stuck (var x)
| stuckL s t : stuck s -> stuck (s t)
| stuckR s t : stuck t -> stuck ((lam s) t).

Hint Constructors stuck.

Lemma L_trichotomy s :
  exactlyOneHolds
    [reducible (≻L) s
     ; abstraction s
     ; stuck s].
Proof.
  Local Ltac trich_tac :=
  repeat intro;repeat 
    lazymatch goal with
    | H: abstraction _ |- _ => inversion_clear H
    | H: stuck (_ _) |- _ => inv H
    | H: ~ reducible (≻L) ?s,  H1 : ?s ≻L _ |- _  => exfalso;eapply H;eexists;exact H1
    | H: reducible (≻L)_ |- _ => destruct H as (?&H);inv H                                                  
    | |- reducible (≻L) _ => hnf;eauto
    end;eauto;easy.
  induction s.
  -exactlyOneHoldsI 3. all:trich_tac.
  -inv_exactlyOneHolds IHs1.
   +exactlyOneHoldsI 1. all:trich_tac.
   +inv_exactlyOneHolds IHs2.
    --exactlyOneHoldsI 1. all:trich_tac.
    --exactlyOneHoldsI 1. all:trich_tac.
    --exactlyOneHoldsI 3. all:trich_tac.
   +exactlyOneHoldsI 3. all:trich_tac.
  -exactlyOneHoldsI 2. all:trich_tac.
Qed.

Lemma stuck_normal s : stuck s -> ~ reducible (≻L) s.
Proof.
  intros ? ?. specialize (L_trichotomy s) as H'. cbn in H'. tauto. 
Qed.

