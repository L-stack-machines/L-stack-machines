Require Export Bool Omega List PrelimsTac Compat.Coq86 (* for Functional Induction*). 

Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Set Warnings "-notation-overridden,-parsing".
Export ListNotations.

(** * Preliminaries *)

(** Decidable predicates. Allows to write e.g. [if Dec (x=y) then _ else _ ] in functions
and [decide (x=y)] in Proofs to do case distinctions after showing that some property is decidable, e,g, see nat_eq_dec *)
Definition dec (X: Prop) : Type := {X} + {~ X}.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.

Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" "_" :=
  destruct (Dec _).


(** ** Natural Numbers *)

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> 
  forall x, p x.

Proof. 
  intros IH x. apply IH. 
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. omega.
    - intros y B. apply IH. intros z C. apply IHn. omega. }
  apply G.
Qed.

Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  le_dec x y.

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).
Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.


(** ** Lists *)
Notation "| A |" := (length A) (at level 65).
(*Notation for lookup*)
Notation "A .[ n ]" := (nth_error A n) (at level 1, format "A '.[' n ]").
Notation "x '∈' A" := (In x A) (at level 70).

(* some lemmas not included in the standard library: *)
Lemma nth_error_lt_Some A (H:list A) n : n < |H| -> exists x, H.[n] = Some x.
Proof.
  intros eq. revert H eq. induction n;intros;destruct H;cbn in *;inv eq;eauto. all:edestruct (IHn H); try omega; eauto.
Qed.

Lemma nth_error_Some_lt A (H:list A) n x : H.[n] = Some x -> n < |H|.
Proof.
  intros eq. revert H eq. induction n;intros;destruct H;cbn in *;inv eq. omega. apply IHn in H1. omega.
Qed.

Lemma nth_error_map A B (H:list A) (f:A->B) n a : (map f H).[n] = Some a -> exists b, H.[n] = Some b /\ a = f b.
Proof.
  intros eq. revert H eq. induction n;intros;destruct H;cbn in *;inv eq. eauto. eauto.
Qed.

Lemma Forall_map X Y (A:list X) p (f:X->Y):
  Forall (fun x => p (f x)) A -> Forall p (map f A).
Proof.
  rewrite !Forall_forall. setoid_rewrite in_map_iff. firstorder subst. eauto.
Qed.

Hint Extern 4 => 
match goal with
|[ H: ?x ∈ nil |- _ ] => destruct H
end.

(* Register additional simplification rules with autorewrite*)
Hint Rewrite <- app_assoc : list.


(** ** Relations *)


Definition rcomp X Y Z (R : X -> Y -> Prop) (S : Y -> Z -> Prop) : X -> Z -> Prop :=
  fun x z => exists y, R x y /\ S y z.


Structure ARS :=
  {
    ARS_X :> Type ;
    ARS_R : ARS_X -> ARS_X -> Prop
  }.
Notation "(≻)" := (@ARS_R _) (at level 0).
Notation "(≻ X )" := (@ARS_R X) (at level 0).
Notation "x  ≻  x'" := (ARS_R x x') (at level 40).

Definition reducible (X : Type) (R : X -> X -> Prop) x :=
  exists x', R x x'.

Hint Unfold reducible.

Definition functional (X Y : Type) (R : X -> Y -> Prop) :=
  forall x y y', R x y -> R x y' -> y = y'.

Definition stepFunction {X Y} (R: X -> Y -> Prop) f :=
  forall x, match f x with
         Some y => R x y
       | None => forall y, ~ R x y
       end.

Definition computable {X Y} (R:X -> Y -> Prop) :=
  exists f, stepFunction R f.

Definition classical {X} R := forall s : X, reducible R s \/ ~ reducible R s.

Lemma computable_classical X (R:X -> X -> Prop):
  computable R -> classical R.
Proof.
  intros [f C] x. specialize (C x). destruct (f x). now left; eauto. right;intros [? ?]. eapply C. eauto.
Qed.

(* missing facts about relation extension on lists *)
Lemma Forall2_impl X Y (P1 P2:X->Y->Prop) A B: (forall x y, P1 x y -> P2 x y) -> Forall2 P1 A B -> Forall2 P2 A B.
Proof.
  intros ? H. induction H;cbn in *;eauto.
Qed.

Inductive terminatesOn (X : Type) (R : X -> X -> Prop) x: Prop :=
  terminatesC (wf: forall x', R x x' -> terminatesOn R x').

Reserved Notation "x  ▷  z" (at level 40).

Inductive evaluates (X : ARS) : X -> X -> Prop :=
  evaluates_B (x : X) : ~ reducible (≻) x -> x ▷ x
|  evaluates_S (x y z : X) : x ≻ y -> y ▷ z -> x ▷ z
where "x ▷ z" := (@evaluates _ x z).

Notation "(▷)" := (@evaluates _) (at level 0).
Notation "(▷ X )" := (@evaluates X) (at level 0).
(* workaround to prefere "x ≻ y" over "(≻) x y"*) Notation "x ▷ x'" := 0.
Notation "x ▷ x'" := (@evaluates _ x x').


Definition normalizes (X : ARS) (x:X) :=
  exists y, x ▷ y.
Hint Unfold normalizes.  

Lemma evaluates_fun (X : ARS) :
  functional (≻X) -> functional  (▷X).
Proof.
  intros FN x x' x'' H. revert x''. induction H.
  - intros. inv H0.
    + reflexivity.
    + destruct H; eauto.
  - intros. inv H1.
    + destruct H2; eauto.
    + eapply IHevaluates. now rewrite (FN _ _ _ H H2).
Qed.

Lemma normalizes_terminates (X : ARS) :
  functional (≻X) ->
  forall (x:X), normalizes x -> terminatesOn (≻) x.
Proof.
  intros FN x [x' ?]. induction H.
  - econstructor. intros x' ?; destruct H. eauto.
  - econstructor. intros x' ?. now rewrite (FN _ _ _ H1 H).
Qed.

Lemma terminates_normalizes (X : ARS) :
  computable (≻X) ->
  forall (x:X), terminatesOn (≻) x -> normalizes x.
Proof.
  intros C%computable_classical x. induction 1. 
  destruct (C x) as [ [a' Hstep] | ].
  - destruct (H _ Hstep) as [a'']. exists a''. eauto using evaluates. 
  - exists x. now econstructor. 
Qed.

Lemma evaluates_irred (X : ARS) (x y : X):
  x ▷ y -> ~ reducible (≻) y.
Proof.
  induction 1; eauto.
Qed.     

(** ** Misc *)

Fixpoint noneHolds (Ps :list Prop) : Prop :=
  match Ps with
  | [] => True
  | P :: Ps => ~ P /\ noneHolds Ps
  end.

Fixpoint exactlyOneHolds (Ps :list Prop) : Prop :=
  match Ps with
  | [] => False
  | P :: Ps => P /\ noneHolds Ps \/ ~ P /\ exactlyOneHolds Ps
  end.

Ltac noneHoldsI :=
  lazymatch goal with
    |- noneHolds [] => now constructor
  | |- noneHolds (_::_) => split;[|noneHoldsI]
  end.

Ltac exactlyOneHoldsI n :=
  lazymatch n with
  | 1 =>  left;split;[|noneHoldsI]
  | S ?n => right;split;[|exactlyOneHoldsI n]
  end.

Ltac inv_noneHolds H :=
  lazymatch type of H with
  | noneHolds [] => clear H
  | noneHolds (_::_) => let tmp := fresh "tmp" in destruct H as [? tmp];inv_noneHolds tmp
  end.

Ltac inv_exactlyOneHolds H :=
  lazymatch type of H with
  | exactlyOneHolds [] => now inversion H
  | exactlyOneHolds (_::_) => let tmp := fresh "tmp" in destruct H as [[? tmp]|[? tmp]];[inv_noneHolds tmp|inv_exactlyOneHolds tmp]
  end.

(** Nicer Notation for Option *)
Notation "'try' x ':='  t 'in' u":=
  (match t with Some x => u | None => None end)
    (at level 200, right associativity).
