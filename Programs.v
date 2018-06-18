From LM Require Import Prelims L.
(** * Programms *)

Inductive Pro := retT | varT (n:nat) (P:Pro) | appT (P:Pro) | lamT (Q P:Pro).

Fixpoint γ (s: L.term) P: Pro :=
  match s with
    var n => varT n P
  | app s t => γ s (γ t (appT P))
  | lam s => lamT (γ s retT) P
  end.

(* Implicit Types A B : list term. *)

Function δ P A: option (list term) :=
  match P with
    retT => Some A
  | varT n P => δ P (var n::A)
  | lamT Q P => match δ Q [] with
               | Some [s] => δ P (lam s::A)
               | _ => None
               end
  | appT P => match A with
               t::s::A => δ P (app s t::A)
             | _ => None
             end
  end.

Lemma decompile_correct' s P A:
  δ (γ s P) A = δ P (s::A).
Proof.
  induction s in P,A|-*. all:cbn.
  -congruence.
  -repeat rewrite append_assoc. rewrite IHs1. cbn. rewrite IHs2. reflexivity.
  -specialize (IHs retT []).
   rewrite IHs. reflexivity.
Qed.

Definition repsP P s := δ P [] = Some [s].
Notation "P ≫P s" := (repsP P s ) (at level 70).
Notation "(>>P)" := repsP (at level 0).

Lemma decompile_append P A A' B:
  δ P A = Some A' -> δ P (A++B) = Some (A'++B).
Proof.
  revert B A'. functional induction (δ P A);intros B A'. all:try congruence;intros eq;cbn in *.
  -congruence.
  -erewrite IHo. all:eauto.
  -rewrite e0. erewrite IHo0. all:eauto.
  -erewrite IHo. all:eauto.    
Qed.

(** Some lemmas to simplify reasoning *)

Lemma decompile_lamT_inv P Q A B:
  δ (lamT Q P) A = Some B -> exists s, δ Q [] = Some [s] /\ δ P (lam s::A) = Some B.
Proof.
  functional inversion 1. subst. cbn. rewrite H3. eauto.
Qed.


Fixpoint substP P (k:nat) R: Pro :=
  match P with
    retT => retT
  | varT n P => if Dec (n=k) then lamT R (substP P k R) else varT n (substP P k R)
  | lamT Q P => lamT (substP Q (S k) R ) (substP P k R)
  | appT P => appT (substP P k R)
  end.

Lemma substP_rep_subst' Q R t k A B:
  R ≫P t
  -> δ Q A = Some B
  -> δ (substP Q k R) (map (fun s => subst s k (lam t)) A)
    = Some (map (fun s => subst s k (lam t)) B).
Proof.
  revert k B. functional induction (δ Q A);intros k B repR repQ. all:try congruence.
  all:cbn in *.
  -congruence.
  -erewrite <- IHo. 2,3:now eassumption.
   cbn. decide _. all:cbn.
   +rewrite repR. reflexivity.
   +reflexivity.
  -erewrite IHo. 2-3:eassumption. cbn. apply IHo0. all:eassumption.
  -apply IHo. all:eassumption.
Qed.

Reserved Notation "P <P k" (at level 70).

Inductive boundP : Pro -> nat -> Prop :=
  boundP_ret k : retT <P k
| boundP_var k n P : n < k -> P <P k -> varT n P <P k
| boundP_lam k P Q : Q <P S k -> P <P k -> lamT Q P <P k
| boundP_app k P : P <P k -> appT P <P k
where "P <P k" := (boundP P k).
Notation "'(<P' k ')'" := (fun P => P <P k) (at level 0, format "'(<P'  k ')'").

Hint Constructors boundP.

Definition closedP P:= P <P 0.
Hint Unfold closedP.

Lemma bound_compile k s P: s <L k -> P <P k -> γ s P <P k.
Proof.
  induction 1 in P|-*;intros bnd;cbn. all:eauto.
Qed.
