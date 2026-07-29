From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris_examples.logrel.F_mu_ref_conc Require Import rules.
From iris_examples.logrel.F_mu_ref_conc.binary Require Import soundness rules.

Definition fact : expr :=
  Rec (If (BinOp Eq (Var 1) (#n 0))
          (#n 1)
          (BinOp Mult (Var 1) (App (Var 0) (BinOp Sub (Var 1) (#n 1))))).

Lemma fact_typed : [] ⊢ₜ fact : TArrow TInt TInt.
Proof. repeat econstructor. Qed.

Definition fact_acc_body : expr :=
  Rec (Lam
         (If (BinOp Eq (Var 2) (#n 0))
             (Var 0)
             (LetIn
                (BinOp Mult (Var 2) (Var 0))
                (LetIn
                   (BinOp Sub (Var 3) (#n 1))
                   (App (App (Var 3) (Var 0)) (Var 1))
                )
             )
         )
      ).

Lemma fact_acc_body_typed : [] ⊢ₜ fact_acc_body : TArrow TInt (TArrow TInt TInt).
Proof. repeat econstructor. Qed.

Lemma fact_acc_body_subst f : fact_acc_body.[f] = fact_acc_body.
Proof. by asimpl. Qed.

Global Hint Rewrite fact_acc_body_subst : autosubst.

Lemma fact_acc_body_unfold :
  fact_acc_body =
  Rec (Lam
         (If (BinOp Eq (Var 2) (#n 0))
             (Var 0)
             (LetIn
                (BinOp Mult (Var 2) (Var 0))
                (LetIn
                   (BinOp Sub (Var 3) (#n 1))
                   (App (App (Var 3) (Var 0)) (Var 1))
                )
             )
         )
      ).
Proof. trivial. Qed.

Global Typeclasses Opaque fact_acc_body.
Global Opaque fact_acc_body.

Definition fact_acc : expr :=
  Lam (App (App fact_acc_body (Var 0)) (#n 1)).

Lemma fact_acc_typed : [] ⊢ₜ fact_acc : TArrow TInt TInt.
Proof.
  repeat econstructor.
  apply (closed_context_weakening [_] []); eauto.
  apply fact_acc_body_typed.
Qed.

Section fact_equiv.
  Context `{heapIG Σ, cfgSG Σ}.

  Lemma fact_fact_acc_refinement :
    ⊢ [] ⊨ fact ≤log≤ fact_acc : (TArrow TInt TInt).
  Proof.
    rewrite bin_log_related_unseal.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %?; destruct vs; simplify_eq.
    iClear "HΔ". simpl.
    iIntros (j K) "Hj"; simpl.
    iApply wp_value; iExists (LamV _); iFrame.
    rewrite /= -/fact.
    iModIntro. iIntros ([? ?] [n [? ?]]); simpl in *; simplify_eq; simpl.
    clear j K.
    iIntros (j K) "Hj"; simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
    asimpl.
    iApply (wp_mono _ _ _ (λ v, ∃ m, j ⤇ fill K (#n (1 * m)) ∗ ⌜v = #nv m⌝))%I.
    { iIntros (?). iDestruct 1 as (m) "[Hm %]"; subst.
      replace (1 * m)%Z with m by lia.
      iExists (#nv _); iFrame; eauto. }
    generalize 1%Z as l => l.
    iLöb as "IH" forall (n l).
    destruct (decide (n = 0)%Z) as [->|].
    - iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl; asimpl.
      rewrite fact_acc_body_unfold.
      iMod (do_step_pure _ _ (AppLCtx _ :: _) with "[$Hj]") as "Hj"; auto.
      rewrite -fact_acc_body_unfold.
      simpl; asimpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iApply (wp_bind (fill [IfCtx _ _])).
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl.
      iApply wp_value. simpl.
      iMod (do_step_pure _ _ (IfCtx _ _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iApply wp_value.
      iExists 1%Z. replace (l * 1)%Z with l by lia.
      auto.
    - iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl; asimpl.
      rewrite fact_acc_body_unfold.
      iMod (do_step_pure _ _ (AppLCtx _ :: _) with "[$Hj]") as "Hj"; auto.
      rewrite -fact_acc_body_unfold.
      simpl; asimpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iApply (wp_bind (fill [IfCtx _ _])).
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl.
      iApply wp_value. simpl.
      destruct (decide (n = 0)%Z); first lia.
      rewrite bool_decide_eq_false_2; last done.
      iMod (do_step_pure _ _ (IfCtx _ _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl.
      destruct (decide (n = 0)%Z); first lia.
      rewrite bool_decide_eq_false_2; last done.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      asimpl.
      iApply (wp_bind (fill [BinOpRCtx _ (#nv _)])).
      iApply (wp_bind (fill [AppRCtx (RecV _)])).
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl; iApply wp_value; simpl.
      iMod (do_step_pure _ _ (LetInCtx _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      asimpl.
      iMod (do_step_pure _ _ (LetInCtx _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      asimpl.
      iApply wp_wand_r; iSplitL; first iApply ("IH" with "[Hj]"); eauto.
      iIntros (v). iDestruct 1 as (m) "[H %]"; simplify_eq.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl; iApply wp_value.
      iExists _; iSplit; last done.
      replace (l * (n * m))%Z with (n * l * m)%Z by lia.
      iFrame.
  Qed.

  Lemma fact_acc_fact_refinement :
    ⊢ [] ⊨ fact_acc ≤log≤ fact : (TArrow TInt TInt).
  Proof.
    rewrite bin_log_related_unseal.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %?; destruct vs; simplify_eq.
    iClear "HΔ". simpl.
    iIntros (j K) "Hj"; simpl.
    iApply wp_value; iExists (RecV _); iFrame.
    iModIntro. iIntros ([? ?] [n [? ?]]); simpl in *; simplify_eq; simpl.
    clear j K.
    iIntros (j K) "Hj"; simpl.
    iApply wp_pure_step_later; auto.
    iIntros "!> _"; asimpl.
    rewrite -/fact.
    iApply (wp_mono _ _ _ (λ v, ∃ m, j ⤇ fill K (#n m) ∗ ⌜v = #nv (1 * m)⌝))%I.
    { iIntros (?). iDestruct 1 as (m) "[? %]"; simplify_eq.
      replace (1 * m)%Z with m by lia.
      iExists (#nv _); iFrame; eauto. }
    generalize 1%Z as l => l.
    iLöb as "IH" forall (K n l).
    destruct (decide (n = 0)) as [->|].
    - rewrite fact_acc_body_unfold.
      iApply (wp_bind (fill [AppLCtx _])).
      iApply wp_pure_step_later; auto.
      rewrite -fact_acc_body_unfold.
      iIntros "!> _"; simpl; asimpl.
      iApply wp_value; simpl.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl; asimpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      simpl; asimpl.
      iMod (do_step_pure _ _ (IfCtx _ _ :: _) with "[$Hj]") as "Hj"; auto.
      iApply (wp_bind (fill [IfCtx _ _])).
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl.
      iApply wp_value. simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl.
      iApply wp_value.
      iExists 1%Z. replace (l * 1)%Z with l by lia; auto.
    - rewrite {2}fact_acc_body_unfold.
      iApply (wp_bind (fill [AppLCtx _])).
      iApply wp_pure_step_later; auto.
      rewrite -fact_acc_body_unfold.
      iIntros "!> _"; simpl; asimpl.
      iApply wp_value; simpl.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl; asimpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      simpl.
      iApply (wp_bind (fill [IfCtx _ _])).
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl.
      iApply wp_value. simpl.
      destruct (decide (n = 0)%Z); first lia.
      rewrite bool_decide_eq_false_2; last done.
      iMod (do_step_pure _ _ (IfCtx _ _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl.
      destruct (decide (n = 0)%Z); first lia.
      rewrite bool_decide_eq_false_2; last done.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iMod (do_step_pure _ _ (AppRCtx (RecV _):: BinOpRCtx _ (#nv _) :: _)
              with "[$Hj]") as "Hj"; eauto.
      simpl.
      iApply (wp_bind (fill [LetInCtx _])).
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl; iApply wp_value; simpl.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl. asimpl.
      iApply (wp_bind (fill [LetInCtx _])).
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl; iApply wp_value; simpl.
      iApply wp_pure_step_later; auto.
      iIntros "!> _"; simpl. asimpl.
      iApply wp_fupd.
      iApply wp_wand_r; iSplitL;
        first iApply ("IH" $! (BinOpRCtx _ (#nv _) :: K) with "[$Hj]"); eauto.
      iIntros (v). iDestruct 1 as (m) "[Hj %]"; simplify_eq.
      simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      simpl.
      iModIntro.
      iExists _; iSplit; first by iFrame.
      replace (l * (n * m))%Z with (n * l * m)%Z by lia.
      done.
  Qed.

End fact_equiv.

Theorem fact_ctx_equiv :
  [] ⊨ fact ≤ctx≤ fact_acc : (TArrow TInt TInt) ∧
  [] ⊨ fact_acc ≤ctx≤ fact : (TArrow TInt TInt).
Proof.
  set (Σ := #[invΣ ; gen_heapΣ loc val ; soundness_binaryΣ]).
  set (HG := soundness.HeapPreIG Σ _ _).
  split.
  - eapply (binary_soundness Σ _); auto using fact_acc_typed, fact_typed.
    intros; apply fact_fact_acc_refinement.
  -  eapply (binary_soundness Σ _); auto using fact_acc_typed, fact_typed.
    intros; apply fact_acc_fact_refinement.
Qed.
