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

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) constr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
    iIntros (v) Hv.

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
      smart_wp_bind (PairLCtx _.[env_subst vs]) v "# Hv" "IH".
      smart_wp_bind (PairRCtx v) v' "# Hv'" "IH1".
      iApply wp_value; eauto 10.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" "IH"; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" "IH"; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" "IH". by iApply wp_value; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" "IH". by iApply wp_value; eauto.
    - (* case *)
      iDestruct (interp_env_length with "[]") as %Hlen; auto.
      smart_wp_bind (CaseCtx _ _) v "# Hv" "IH"; cbn.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; subst.
      + simpl. iApply wp_pure_step_later; auto. asimpl.
        iApply ("IH1" $! (w::vs)).
        iNext. iApply interp_env_cons; by iSplit.
      + simpl. iApply wp_pure_step_later; auto. asimpl.
        iApply ("IH2" $! (w::vs)).
        iNext. iApply interp_env_cons; by iSplit.
    - (* lam *)
      iDestruct (interp_env_length with "[]") as %Hlen; auto.
      iApply wp_value. simpl. iModIntro; iIntros (w) "#Hw".
      iApply wp_pure_step_later; auto.
      asimpl.
      iNext; iApply ("IH" $! (w :: vs)). iApply interp_env_cons; by iSplit.
    - (* app *)
      smart_wp_bind (AppLCtx (_.[env_subst vs])) v "#Hv" "IH".
      smart_wp_bind (AppRCtx v) w "#Hw" "IH1".
      iApply "Hv"; auto.
  Qed.
End typed_interp.
