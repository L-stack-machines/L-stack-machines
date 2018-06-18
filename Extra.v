Require Import Prelims Refinements L Programs Closures M_clos Codes Heaps M_heap.

(** * Extras  *)
Lemma stuck_not_closed s :
  stuck s -> closedL s -> False.
Proof.
  induction 1;inversion 1;eauto;omega.
Qed.

Lemma closed_cases s :
  closedL s -> exactlyOneHolds [reducible (≻L) s;abstraction s].
Proof.
  intros ?. specialize stuck_not_closed with (s:=s). specialize L_trichotomy with (s:=s). cbn. tauto. 
Qed.

(** ** Counterexample with open terms for closure machine **)

  Inductive star X (R:X->X->Prop) : X -> X -> Prop :=
  | starR x : star R x x
  | starC x y z : R x y -> star R y z -> star R x z.
  
  Lemma counterexample_closed_needed:
    let s := (lam (lam 1)) (lam 1) (lam 0)in
    star (≻L) s (lam (lam 0)) /\
    star (≻C) ([γ s retT/[]],[]) ([],[varT 1 retT / []]).
          Proof.
            split.
            -repeat (eapply starC;[now eauto|cbn]). apply starR.
            -cbn. repeat (eapply starC;[do 2 econstructor;now constructor|cbn]). apply starR. 
          Qed.

(** ** Properties of closedness *)

Lemma boundL_mono k k' s : k <= k' -> s <L k -> s <L k'.
Proof.
  intros HMk. induction 1 in HMk,k'|-*; econstructor; eauto. 
  - omega.
  - eapply IHboundL. omega.
Qed.

Lemma boundL_subst s t k : s <L S k -> t <L k -> subst s k t <L k.
Proof.
  revert k t; induction s; intros k t cls_s cls_t; simpl; inv cls_s; eauto 6 using boundL_mono.
  decide (n = k); eauto. econstructor.  omega.
Qed.

Lemma subst_boundL_inv s k u : s <L k -> subst s k u = s.
Proof with eauto.
  intros H; revert u; induction H; intros u; simpl.
  - decide (n = k)... omega.
  - rewrite IHboundL1, IHboundL2...
  - f_equal...
Qed.

Lemma closed_subst s k u : closedL s -> subst s k u = s.
Proof.
  intros H. eapply subst_boundL_inv. eapply boundL_mono. 2:eassumption. omega.
Qed.
  
Lemma closed_stepL s t : s ≻L t -> closedL s -> closedL t.
Proof.
  unfold closedL;induction 1; intros cls_s; inv cls_s; eauto using boundL.
  inv H1. eauto using boundL_subst.
Qed.

(** ** Weak computability of heap decompilation *)

Section heap_decomp.
  Variable codeImpl:code.
  Variable heapImpl:heap PA.

  Variable C: Code.

  Notation "(≫C_ H )" := (representsClos C H) (at level 0, format "'(≫C_' H ')'").
  Notation "g ≫C_ H e" := (representsClos C H g e) (at level 70,H at level 0, format "g  '≫C_' H  e").
  Notation "a ≫E_ H E" := (representsEnv C H a E) (at level 70,H at level 0, format "a  '≫E_' H  E").

  Notation "(≫HC)" := (repsHC) (at level 0).
  Notation "ψ '≫HC' π" := (repsHC ψ π) (at level 70).

  (** ** Decompilation Function*)
  Section unlinPro.

    Fixpoint unlinPro (i:nat) (p:PA) : option Pro :=
      match i,C p with
      | S i, Some (appC) =>  match unlinPro i (inc p) with
                              Some P => Some (appT P)
                            | _ => None
                            end
      | S i, Some (varC x) => match unlinPro i (inc p) with
                               Some P => Some (varT x P)
                             | _ => None
                             end
      | S i, Some (retC) => Some retT
      | S i, Some (lamC q) => match unlinPro i (inc p),unlinPro i q with
                               Some P,Some Q => Some (lamT Q P)
                             | _,_ => None
                             end
      | _,_ => None
      end.
    
  Lemma unlinPro_mono i j p P: i <= j -> unlinPro i p = Some P -> unlinPro j p = Some P.
  Proof.
    induction j in i,p,P|-*.
    -destruct i. all:easy. 
    -destruct i. easy.
     +intros H%le_S_n eq.
      specialize IHj with (1:=H).
      cbn in eq|-*. 
      destruct (C p) as [[]|] eqn:eq'.
      1,5:congruence.
      all:repeat (let eq := fresh "eq" in destruct (unlinPro i _) eqn:eq;[apply IHj in eq;try eassumption;rewrite eq in *|congruence]). 
      all:congruence. 
  Qed.

  Lemma unlinPro_fuel p P: p ≫p_C P -> exists i, unlinPro i p = Some P.
  Proof.
    induction 1 as [? eq| ? ? ? eq ? (i1&IH)| ? ? ? ? eq ? (i1&IH1) ? (i2&IH2)| ? ? ? eq (i1&IH)].
    -exists 1. cbn. now rewrite eq. 
    -exists (1+i1). cbn. now rewrite eq,IH. 
    -exists (1+i1+i2). cbn. rewrite eq. do 2 (erewrite unlinPro_mono;[| |eassumption];[|omega]). reflexivity.
    -exists (1+i1). cbn. now rewrite H,IH.
  Qed.

  End unlinPro.

  Section unlinEnv.
    
    Variable H:Heap.

    Fixpoint unlinClos (i:nat) (p:HC) : option Clo :=
      match i,p with
        0,_ => None
      | S i,(p,a) =>
        match unlinPro i p, unlinEnv i a with
          Some P, Some E => Some (P/E)
        | _,_ => None
        end
      end
    with
    unlinEnv (i:nat) (a:HA) : option (list Clo) :=
      match i with
        0 => None
      | S i => match get H a with
                None => None
              | Some None => Some []
              | Some (Some (p,b)) =>
                match unlinClos i p,unlinEnv i b with
                | Some C, Some A => Some (C::A)
                | _,_ => None
                end
              end
      end.

    Lemma unlinEnv_mono i j: i <= j -> (forall g e, unlinClos i g = Some e -> unlinClos j g = Some e)
                                     /\ forall a E, (unlinEnv i a = Some E -> unlinEnv j a = Some E). 
    Proof.
      induction j in i|-*.
      -destruct i. all:easy. 
      -destruct i. easy. intros H1%le_S_n. specialize IHj with (1:=H1) as [IHc ILEnv].
       split;cbn. 
       +intros [? ?] ?.
        destruct unlinPro eqn:eq. 2:easy. rewrite unlinPro_mono with (1:=H1) (2:=eq).
        destruct unlinEnv eqn:eq1. 2:easy. rewrite ILEnv with (1:=eq1). easy. 
       +intros ? ?. destruct (H a) as [[[]|]|]. 2,3:easy.
        destruct unlinClos eqn: eq. 2:easy. rewrite IHc with (1:=eq).
        destruct unlinEnv eqn:eq2. 2:easy. rewrite ILEnv with (1:=eq2). easy.
    Qed.

    Lemma unlinEnv_fuel: (forall a E, a ≫E_H E -> exists n, unlinEnv n a = Some E).
    Proof.
      induction 1 as [? eq|? ? ? ? ? ? ? eq Rp ? [n1 eq1] ? [n2 eq2]].
      -exists 1. cbn. now rewrite eq.
      -apply unlinPro_fuel in Rp as [n3 eq3].
       eexists (2 + n1 + n2 + n3). cbn. rewrite eq. 
       eapply unlinEnv_mono in eq1 as ->. 2:omega.
       eapply unlinPro_mono in eq3 as ->. 2:omega.
       eapply unlinEnv_mono with (j:= S (n1+n2+n3)) in eq2. 2:omega.  cbn in eq2. rewrite eq2. tauto.
    Qed.
    (*
    Lemma unlinEnv_fuel: (forall a E, a ≫E_H E -> exists n, unlinEnv n a = Some E)
                         /\ (forall g e, g ≫C_H e -> exists n,  unlinClos n g = Some e). 
    Proof.
      apply unheaped_mutual_ind.
      -intros ? ? ? ? ? eq ? [n1 eq1] ? [n2 eq2].
       exists (1+n1+n2). cbn in *. rewrite eq.
       eapply unlinEnv_mono in eq1. rewrite eq1. 2:omega.
       eapply unlinEnv_mono in eq2. rewrite eq2. 2:omega.
       easy.
      -intros ? eq. exists 1. cbn in *. now rewrite eq.
      -intros ? ? ? ? ? [n1 eq1] Rep.
       eapply unlinPro_fuel in Rep as [n2 eq2].
       exists (1+n1+n2). cbn. erewrite unlinPro_mono with (2:=eq2). 2:omega. eapply unlinEnv_mono in eq1. rewrite eq1. 2:omega. tauto.
    Qed.
*)
  End unlinEnv. 
  
End heap_decomp.
