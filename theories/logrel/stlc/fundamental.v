From iris.proofmode Require Import proofmode.
From iris_examples.logrel.stlc Require Import rules.
From iris.program_logic Require Import lifting.
From iris_examples.logrel.stlc Require Export logrel.
From iris.prelude Require Import options.

Definition log_typed `{irisGS stlc_lang Σ}
           (Γ : list type) (e : expr) (τ : type) : iProp Σ :=
  □∀ vs, ⟦ Γ ⟧* vs -∗ ⟦ τ ⟧ₑ e.[env_subst vs].
Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Section typed_interp.
  (** STLC is somewhat unusual in that we quantify over an arbitrary [irisGS] --
  almost all languages need to have a specific [irisGS] instance to fix their
  specific [state_interp], but STLC has no state so it does not care. *)
  Context `{irisGS stlc_lang Σ}.

  Lemma interp_expr_bind K e τ τ' :
    ⟦ τ ⟧ₑ e -∗ (∀ v, ⟦ τ ⟧ v -∗ ⟦ τ' ⟧ₑ (fill K (#v))) -∗ ⟦ τ' ⟧ₑ (fill K e).
  Proof. iIntros; iApply wp_bind; iApply (wp_wand with "[$]"); done. Qed.

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e : τ.
  Proof.
    intros Htyped.
    iInduction Htyped as [] "IH"; iIntros (vs) "!# #Hctx /=".
    - (* var *)
      iDestruct (interp_env_Some_l with "[]") as (v) "[#H1 #H2]"; eauto;
        iDestruct "H1" as %Heq. erewrite env_subst_lookup; eauto.
      by iApply wp_value.
    - (* unit *) by iApply wp_value.
    - (* pair *)
      iApply (interp_expr_bind [PairLCtx _]); first by iApply "IH".
      iIntros (v) "#Hv /=".
      iApply (interp_expr_bind [PairRCtx _]); first by iApply "IH1".
      iIntros (w) "#Hw /=".
      iApply wp_value; simpl; eauto 10.
    - (* fst *)
      iApply (interp_expr_bind [FstCtx]); first by iApply "IH".
      iIntros (v) "#Hv /=".
      iDestruct "Hv" as (w1 w2) "#[-> [H2 H3]] /=".
      iApply wp_pure_step_later; auto. iIntros "!> _". by iApply wp_value.
    - (* snd *)
      iApply (interp_expr_bind [SndCtx]); first by iApply "IH".
      iIntros (v) "#Hv /=".
      iDestruct "Hv" as (w1 w2) "#[-> [H2 H3]] /=".
      iApply wp_pure_step_later; auto. iIntros "!> _". by iApply wp_value.
    - (* injl *)
      iApply (interp_expr_bind [InjLCtx]); first by iApply "IH".
      iIntros (v) "#Hv /=".
      iApply wp_value; simpl; eauto.
    - (* injr *)
      iApply (interp_expr_bind [InjRCtx]); first by iApply "IH".
      iIntros (v) "#Hv /=".
      iApply wp_value; simpl; eauto.
    - (* case *)
      iDestruct (interp_env_length with "[]") as %Hlen; auto.
      iApply (interp_expr_bind [CaseCtx _ _]); first by iApply "IH".
      iIntros (v) "#Hv /=".
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[-> Hw] /=".
      + simpl. iApply wp_pure_step_later; auto. asimpl.
        iIntros "!> _". iApply ("IH1" $! (w::vs)).
        iApply interp_env_cons; by iSplit.
      + simpl. iApply wp_pure_step_later; auto. asimpl.
        iIntros "!> _". iApply ("IH2" $! (w::vs)).
        iApply interp_env_cons; by iSplit.
    - (* lam *)
      iDestruct (interp_env_length with "[]") as %Hlen; auto.
      iApply wp_value. simpl. iModIntro; iIntros (w) "#Hw".
      iApply wp_pure_step_later; auto. iIntros "!> _". asimpl.
      iApply ("IH" $! (w :: vs)). iApply interp_env_cons; by iSplit.
    - (* app *)
      iApply (interp_expr_bind [AppLCtx _]); first by iApply "IH".
      simpl.
      iIntros (v) "#Hv /=".
      iApply (interp_expr_bind [AppRCtx _]); first by iApply "IH1".
      iIntros (w) "#Hw/=".
      iApply "Hv"; auto.
  Qed.
End typed_interp.
