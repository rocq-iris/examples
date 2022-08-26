From iris.algebra Require Import list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export lifting.
From iris_examples.logrel.F_mu_ref_conc.binary Require Export logrel rules.
From iris.prelude Require Import options.

Section bin_log_def.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).

  Definition bin_log_related (Γ : list type) (e e' : expr) (τ : type) : iProp Σ :=
    tc_opaque (□ ∀ Δ vvs,
      spec_ctx ∧ ⟦ Γ ⟧* Δ vvs -∗
      ⟦ τ ⟧ₑ Δ (e.[env_subst (vvs.*1)], e'.[env_subst (vvs.*2)]))%I.

  Global Instance: ∀ Γ e e' τ, Persistent (bin_log_related Γ e e' τ).
  Proof. rewrite/bin_log_related /=. apply _. Qed.

End bin_log_def.

Notation "Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Section fundamental.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).
  Implicit Types e : expr.
  Implicit Types Δ : listO D.
  Local Hint Resolve to_of_val : core.

  (* Put all quantifiers at the outer level *)
  Lemma bin_log_related_alt {Γ e e' τ} Δ vvs j K :
    Γ ⊨ e ≤log≤ e' : τ -∗
    spec_ctx ∗ ⟦ Γ ⟧* Δ vvs ∗ j ⤇ fill K (e'.[env_subst (vvs.*2)])
    -∗ WP e.[env_subst (vvs.*1)] {{ v, ∃ v',
        j ⤇ fill K (of_val v') ∗ interp τ Δ (v, v') }}.
  Proof.
    iIntros "#Hlog (#Hs & HΓ & Hj)".
    iApply ("Hlog" with "[HΓ]"); iFrame; eauto.
  Qed.

   Lemma interp_expr_bind KK ee Δ τ τ' :
    ⟦ τ ⟧ₑ Δ ee -∗
    (∀ vv, ⟦ τ ⟧ Δ vv -∗ ⟦ τ' ⟧ₑ Δ (fill KK.1 (of_val vv.1), fill KK.2 (of_val vv.2))) -∗
    ⟦ τ' ⟧ₑ Δ (fill KK.1 ee.1, fill KK.2 ee.2).
  Proof.
    iIntros "He HK" (j Z) "Hj /=".
    iSpecialize ("He" with "[Hj]"); first by rewrite -fill_app; iFrame.
    iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (?); iDestruct 1 as (?) "[? #?]".
    iApply ("HK" $! (_, _)); [done| rewrite /= fill_app //].
  Qed.

  Lemma interp_expr_bind' K K' e e' Δ τ τ' :
    ⟦ τ ⟧ₑ Δ (e, e') -∗
    (∀ vv, ⟦ τ ⟧ Δ vv -∗ ⟦ τ' ⟧ₑ Δ (fill K (of_val vv.1), fill K' (of_val vv.2))) -∗
    ⟦ τ' ⟧ₑ Δ (fill K e, fill K' e').
  Proof. iApply (interp_expr_bind (_, _) (_, _)). Qed.

  Lemma interp_expr_val vv Δ τ : ⟦ τ ⟧ Δ vv -∗ ⟦ τ ⟧ₑ Δ (of_val vv.1, of_val vv.2).
  Proof. destruct vv; iIntros "?" (? ?) "?"; iApply wp_value; iExists _; iFrame. Qed.

  Lemma bin_log_related_var Γ x τ :
    Γ !! x = Some τ → ⊢ Γ ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (? Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_Some_l with "HΓ") as ([v v']) "[Heq ?]"; first done.
    iDestruct "Heq" as %Heq.
    erewrite !env_subst_lookup; rewrite ?list_lookup_fmap ?Heq; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_unit Γ : ⊢ Γ ⊨ Unit ≤log≤ Unit : TUnit.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists UnitV; eauto.
  Qed.

  Lemma bin_log_related_nat Γ n : ⊢ Γ ⊨ #n n ≤log≤ #n n : TNat.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (#nv _); eauto.
  Qed.

  Lemma bin_log_related_bool Γ b : ⊢ Γ ⊨ #♭ b ≤log≤ #♭ b : TBool.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (#♭v _); eauto.
  Qed.

  Lemma bin_log_related_pair Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [PairLCtx _] [PairLCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "Hvv".
    iApply (interp_expr_bind' [PairRCtx _] [PairRCtx _]); first by iApply "IH2"; iFrame "#".
    iIntros ([w w']) "Hww".
    iApply (interp_expr_val (PairV _ _, PairV _ _)).
    iExists (v, v'), (w, w'); simpl; repeat iSplit; trivial.
  Qed.

  Lemma bin_log_related_fst Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : TProd τ1 τ2 -∗ Γ ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [FstCtx] [FstCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "Hvv"; cbn [interp].
    iDestruct "Hvv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq/=.
    iIntros (j K) "Hj /=".
    iApply wp_pure_step_later; eauto. iIntros "!> _".
    iMod (step_fst with "[$]") as "Hw"; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_snd Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : TProd τ1 τ2 -∗ Γ ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [SndCtx] [SndCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "Hvv"; cbn [interp].
    iDestruct "Hvv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iIntros (j K) "Hj /=".
    iApply wp_pure_step_later; eauto. iIntros "!> _".
    iMod (step_snd with "[$]") as "Hw"; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_injl Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : τ1 -∗ Γ ⊨ InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [InjLCtx] [InjLCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "Hvv".
    iApply (interp_expr_val (InjLV _, InjLV _)).
    iLeft; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_injr Γ e e' τ1 τ2 :
      Γ ⊨ e ≤log≤ e' : τ2 -∗ Γ ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [InjRCtx] [InjRCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "Hvv".
    iApply (interp_expr_val (InjRV _, InjRV _)).
    iRight; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_case Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    Γ ⊨ e0 ≤log≤ e0' : TSum τ1 τ2 -∗
    τ1 :: Γ ⊨ e1 ≤log≤ e1' : τ3 -∗
    τ2 :: Γ ⊨ e2 ≤log≤ e2' : τ3 -∗
    Γ ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vvs) "!# #(Hs & HΓ)".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply (interp_expr_bind' [CaseCtx _ _] [CaseCtx _ _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "Hvv /=".
    iIntros (j K) "Hj /=".
    iDestruct "Hvv" as "[Hvv|Hvv]";
    iDestruct "Hvv" as ([w w']) "[% Hw]"; simplify_eq.
    - iApply fupd_wp.
      iMod (step_case_inl with "[$]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. fold of_val. iIntros "!> !> _".
      asimpl.
      iApply (bin_log_related_alt _ ((w,w') :: vvs) with "IH2").
      repeat iSplit; eauto.
      iApply interp_env_cons; auto.
    - iApply fupd_wp.
      iMod (step_case_inr with "[$]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. fold of_val. iIntros "!> !> _".
      asimpl.
      iApply (bin_log_related_alt _ ((w,w') :: vvs) with "IH3").
      repeat iSplit; eauto.
      iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_if Γ e0 e1 e2 e0' e1' e2' τ :
    Γ ⊨ e0 ≤log≤ e0' : TBool -∗
    Γ ⊨ e1 ≤log≤ e1' : τ -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [IfCtx _ _] [IfCtx _ _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "Hvv /=".
    iIntros (j K) "Hj /=".
    iDestruct "Hvv" as ([]) "[% %]"; simplify_eq/=; iApply fupd_wp.
    - iMod (step_if_true _ j K with "[-]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. iIntros "!> !> _".
      iApply (bin_log_related_alt with "IH2"); eauto.
    - iMod (step_if_false _ j K with "[-]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. iIntros "!> !> _".
      iApply (bin_log_related_alt with "IH3"); eauto.
  Qed.

  Lemma bin_log_related_nat_binop Γ op e1 e2 e1' e2' :
    Γ ⊨ e1 ≤log≤ e1' : TNat -∗
    Γ ⊨ e2 ≤log≤ e2' : TNat -∗
    Γ ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : binop_res_type op.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [BinOpLCtx _ _] [BinOpLCtx _ _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "Hvv /=".
    iApply (interp_expr_bind' [BinOpRCtx _ _] [BinOpRCtx _ _]); first by iApply "IH2"; iFrame "#".
    iIntros ([w w']) "Hww /=".
    iIntros (j K) "Hj /=".
    iDestruct "Hvv" as (n) "[% %]"; simplify_eq/=.
    iDestruct "Hww" as (n') "[% %]"; simplify_eq/=.
    iApply fupd_wp.
    iMod (step_nat_binop _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iIntros "!> !> _".
    iApply wp_value. iExists _; iSplitL; eauto.
    destruct op; simpl; try destruct eq_nat_dec; try destruct le_dec;
      try destruct lt_dec; eauto.
  Qed.

  Lemma bin_log_related_rec Γ e e' τ1 τ2 :
    TArrow τ1 τ2 :: τ1 :: Γ ⊨ e ≤log≤ e' : τ2 -∗
    Γ ⊨ Rec e ≤log≤ Rec e' : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_val (RecV _, RecV _)).
    simpl.
    iLöb as "IHL". iIntros ([v v']) "!# #Hiv". iIntros (j' K') "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
    iApply fupd_wp.
    iMod (step_rec _ j' K' _ (of_val v') v' with "[-]") as "Hz"; eauto.
    asimpl. change (Rec ?e) with (of_val (RecV e)).
    iApply (bin_log_related_alt _ ((_,_) :: (v,v') :: vvs) with "IH").
    repeat iSplit; eauto.
    iModIntro.
    rewrite !interp_env_cons; iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_lam Γ e e' τ1 τ2 :
    τ1 :: Γ ⊨ e ≤log≤ e' : τ2 -∗
    Γ ⊨ Lam e ≤log≤ Lam e' : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_val (LamV _, LamV _)).
    simpl.
    iIntros ([v v']) "!# #Hiv". iIntros (j' K') "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
    iApply fupd_wp.
    iMod (step_lam _ j' K' _ (of_val v') v' with "[-]") as "Hz"; eauto.
    asimpl. iFrame "#". change (Lam ?e) with (of_val (LamV e)).
    iApply (bin_log_related_alt _  ((v,v') :: vvs) with "IH").
    repeat iSplit; eauto.
    iModIntro.
    rewrite !interp_env_cons; iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_letin Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    τ1 :: Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ LetIn e1 e2 ≤log≤ LetIn e1' e2': τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply (interp_expr_bind' [LetInCtx _] [LetInCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "#Hvv /=".
    iIntros (j K) "Hj /=".
    iMod (step_letin _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iIntros "!> _".
    asimpl.
    iApply (bin_log_related_alt _ ((v, v') :: vvs) with "IH2").
    repeat iSplit; eauto.
    rewrite !interp_env_cons; iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_seq Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ Seq e1 e2 ≤log≤ Seq e1' e2': τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply (interp_expr_bind' [SeqCtx _] [SeqCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "#Hvv /=".
    iIntros (j K) "Hj /=".
    iMod (step_seq _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iIntros "!> _".
    asimpl.
    iApply (bin_log_related_alt with "IH2"); repeat iSplit; eauto.
  Qed.

  Lemma bin_log_related_app Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ1 -∗
    Γ ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ) /=".
    iApply (interp_expr_bind' [AppLCtx _] [AppLCtx _]); first by iApply "IH1"; iFrame "#".
    simpl.
    iIntros ([v v']) "#Hvv /=".
    iApply (interp_expr_bind' [AppRCtx _] [AppRCtx _]); first by iApply "IH2"; iFrame "#".
    iIntros ([w w']) "#Hww/=".
    iApply ("Hvv" $! (w, w') with "Hww"); simpl; eauto.
  Qed.

  Lemma bin_log_related_tlam Γ e e' τ :
    (subst (ren (+1)) <$> Γ) ⊨ e ≤log≤ e' : τ -∗
    Γ ⊨ TLam e ≤log≤ TLam e' : TForall τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (TLamV _).
    iIntros "{$Hj} /= !#"; iIntros (τi j' K') "Hv /=".
    iApply wp_pure_step_later; auto. iIntros "!> _".
    iApply fupd_wp.
    iMod (step_tlam _ j' K' (e'.[env_subst (vvs.*2)]) with "[-]") as "Hz"; eauto.
    iApply (bin_log_related_alt with "IH"); repeat iSplit; eauto.
    iModIntro.
    rewrite interp_env_ren; auto.
  Qed.

  Lemma bin_log_related_tapp Γ e e' τ τ' :
    Γ ⊨ e ≤log≤ e' : TForall τ -∗ Γ ⊨ TApp e ≤log≤ TApp e' : τ.[τ'/].
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [TAppCtx] [TAppCtx]); first by iApply "IH"; iFrame "#".
    simpl.
    iIntros ([v v']) "#Hvv /=".
    iIntros (j K) "Hj /=".
    iApply wp_wand_r; iSplitL.
    { iSpecialize ("Hvv" $! (interp τ' Δ)). iApply "Hvv"; eauto. }
    iIntros (w). iDestruct 1 as (w') "[Hw Hiw]".
    iExists _; rewrite -interp_subst; eauto.
  Qed.

  Lemma bin_log_related_pack Γ e e' τ τ' :
    Γ ⊨ e ≤log≤ e' : τ.[τ'/] -∗ Γ ⊨ Pack e ≤log≤ Pack e' : TExist τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [PackCtx] [PackCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "#Hvv".
    iApply (interp_expr_val (PackV _, PackV _)).
    rewrite -interp_subst /=.
    iExists (interp _ Δ), (_, _); iSplit; done.
  Qed.

  Lemma bin_log_related_unpack Γ e1 e1' e2 e2' τ τ' :
    Γ ⊨ e1 ≤log≤ e1' : TExist τ -∗
    τ :: (subst (ren (+1)) <$> Γ) ⊨ e2 ≤log≤ e2' : τ'.[ren (+1)] -∗
    Γ ⊨ UnpackIn e1 e2 ≤log≤ UnpackIn e1' e2' : τ'.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [UnpackInCtx _] [UnpackInCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "#Hvv /=".
    iDestruct "Hvv" as (τi (v1, v2) Hvv) "#Hvv"; simplify_eq /=.
    iIntros (j K) "Hj /=".
    iApply wp_pure_step_later; auto. iIntros "!> _".
    iApply fupd_wp.
    iMod (step_pack with "[Hj]") as "Hj"; eauto.
    asimpl.
    iModIntro.
    iApply wp_wand_r; iSplitL.
    { iApply (bin_log_related_alt (τi :: Δ) ((v1, v2) :: vvs) with "IH2 [$Hj]").
      iFrame; iFrame "#".
      iApply interp_env_cons; iSplit; first done.
      by iApply interp_env_ren. }
    iIntros (w). iDestruct 1 as (v) "[Hj #Hv]".
    iExists _; iFrame.
    by iApply (interp_weaken [] [_]); simpl.
  Qed.

  Lemma bin_log_related_fold Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : τ.[(TRec τ)/] -∗ Γ ⊨ Fold e ≤log≤ Fold e' : TRec τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [FoldCtx] [FoldCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "#Hvv".
    iApply (interp_expr_val (FoldV _, FoldV _)).
    rewrite /= fixpoint_interp_rec1_eq /= -interp_subst.
    iModIntro; iExists (_, _); eauto.
  Qed.

  Lemma bin_log_related_unfold Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : TRec τ -∗ Γ ⊨ Unfold e ≤log≤ Unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [UnfoldCtx] [UnfoldCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "#Hvv".
    iIntros (j K) "Hj /=".
    rewrite /= fixpoint_interp_rec1_eq /=.
    change (fixpoint _) with (interp (TRec τ) Δ).
    iDestruct "Hvv" as ([w w']) "#[% Hiz]"; simplify_eq/=.
    iApply fupd_wp.
    iMod (step_fold _ j K (of_val w') w' with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iIntros "!> !> _".
    iApply wp_value. iExists _; iFrame "Hz". by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_fork Γ e e' :
    Γ ⊨ e ≤log≤ e' : TUnit -∗ Γ ⊨ Fork e ≤log≤ Fork e' : TUnit.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply fupd_wp.
    iMod (step_fork _ j K with "[-]") as (j') "[Hj Hj']"; eauto.
    iApply wp_fork; iModIntro. rewrite -bi.later_sep. iNext; iSplitL "Hj".
    - iExists UnitV; eauto.
    - iApply wp_wand_l; iSplitR; [|iApply (bin_log_related_alt _ _ _ [])]; eauto.
  Qed.

  Lemma bin_log_related_alloc Γ e e' τ :
      Γ ⊨ e ≤log≤ e' : τ -∗ Γ ⊨ Alloc e ≤log≤ Alloc e' : Tref τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [AllocCtx] [AllocCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "#Hvv".
    iIntros (j K) "Hj /=".
    iApply fupd_wp.
    iMod (step_alloc _ j K (of_val v') v' with "[-]") as (l') "[Hj Hl]"; eauto.
    iApply wp_atomic; eauto.
    iApply wp_alloc; eauto. do 2 iModIntro. iNext.
    iIntros (l) "Hl'".
    iMod (inv_alloc (logN .@ (l,l')) _ (∃ w : val * val,
      l ↦ᵢ w.1 ∗ l' ↦ₛ w.2 ∗ interp τ Δ w)%I with "[Hl Hl']") as "HN"; eauto.
    { iNext. iExists (v, v'); iFrame; done. }
    iModIntro; iExists (LocV l'). iFrame "Hj". iExists (l, l'); eauto.
  Qed.

  Lemma bin_log_related_load Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : (Tref τ) -∗ Γ ⊨ Load e ≤log≤ Load e' : τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [LoadCtx] [LoadCtx]); first by iApply "IH"; iFrame "#".
    iIntros ([v v']) "#Hvv".
    iIntros (j K) "Hj /=".
    iDestruct "Hvv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply wp_atomic; eauto.
    iInv (logN .@ (l,l')) as ([w w']) "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    iModIntro.
    iApply (wp_load with "Hw1").
    iNext. iIntros "Hw1".
    iMod (step_load  with "[$]") as "[Hv Hw2]"; first solve_ndisj.
    iMod ("Hclose" with "[Hw1 Hw2]").
    { iNext. iExists (w,w'); by iFrame. }
    iModIntro. iExists w'; by iFrame.
  Qed.

  Lemma bin_log_related_store Γ e1 e2 e1' e2' τ :
    Γ ⊨ e1 ≤log≤ e1' : (Tref τ) -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [StoreLCtx _] [StoreLCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "#Hvv".
    iApply (interp_expr_bind' [StoreRCtx _] [StoreRCtx _]); first by iApply "IH2"; iFrame "#".
    iIntros ([w w']) "#Hww".
    iIntros (j K) "Hj /=".
    iDestruct "Hvv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply wp_atomic; eauto.
    iInv (logN .@ (l,l')) as ([v v']) "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro.
    iApply (wp_store with "Hv1"); auto using to_of_val.
    iNext. iIntros "Hw2".
    iMod (step_store with "[$]") as "[Hw Hv2]"; [done|solve_ndisj|].
    iMod ("Hclose" with "[Hw2 Hv2]").
    { iNext; iExists (w, w'); simpl; iFrame; done. }
    iExists UnitV; iFrame; auto.
  Qed.

  Lemma bin_log_related_CAS Γ e1 e2 e3 e1' e2' e3' τ :
    EqType τ →
    Γ ⊨ e1 ≤log≤ e1' : Tref τ -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ e3 ≤log≤ e3' : τ -∗
    Γ ⊨ CAS e1 e2 e3 ≤log≤ CAS e1' e2' e3' : TBool.
  Proof.
    iIntros (Heqτ) "#IH1 #IH2 #IH3".
    iIntros (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [CasLCtx _ _] [CasLCtx _ _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "#Hvv".
    iApply (interp_expr_bind' [CasMCtx _ _] [CasMCtx _ _]); first by iApply "IH2"; iFrame "#".
    iIntros ([w w']) "#Hww".
    iApply (interp_expr_bind' [CasRCtx _ _] [CasRCtx _ _]); first by iApply "IH3"; iFrame "#".
    iIntros ([u u']) "#Huu".
    iIntros (j K) "Hj /=".
    iDestruct "Hvv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply wp_atomic; eauto.
    iInv (logN.@(l, l')) as ([v v']) "(>Hl & >Hl' & #Hvv) /=" "Hclose".
    iModIntro.
    destruct (decide (v = w)) as [|Hneq]; simplify_eq.
    - iApply (wp_cas_suc with "Hl"); eauto using to_of_val; eauto.
      iNext. iIntros "Hl".
      iMod (interp_EqType_one_to_one with "Hl Hl' Hvv Hww") as "(Hl & Hl' & %)"; first done.
      destruct (decide (v' = w')); simplify_eq; last by intuition simplify_eq.
      iMod (step_cas_suc with "[$]") as "[Hw Hl']"; simpl; eauto; first solve_ndisj.
      iMod ("Hclose" with "[Hl Hl']").
      { iNext; iExists (_, _); by iFrame. }
      iExists (#♭v true); iFrame; eauto.
    - iApply (wp_cas_fail with "Hl"); eauto using to_of_val; eauto.
      iNext. iIntros "Hl".
      iMod (interp_EqType_one_to_one with "Hl Hl' Hvv Hww") as "(Hl & Hl' & %)"; first done.
      destruct (decide (v' = w')); simplify_eq; first by intuition simplify_eq.
      iMod (step_cas_fail with "[$]") as "[Hw Hl']"; simpl; eauto; first solve_ndisj.
      iMod ("Hclose" with "[Hl Hl']").
      { iNext; iExists (_, _); by iFrame. }
      iExists (#♭v false); eauto.
  Qed.

  Lemma bin_log_related_FAA Γ e1 e2 e1' e2' :
    Γ ⊨ e1 ≤log≤ e1' : Tref TNat -∗
    Γ ⊨ e2 ≤log≤ e2' : TNat -∗
    Γ ⊨ FAA e1 e2 ≤log≤ FAA e1' e2' : TNat.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (interp_expr_bind' [FAALCtx _] [FAALCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros ([v v']) "#Hvv".
    iApply (interp_expr_bind' [FAARCtx _] [FAARCtx _]); first by iApply "IH2"; iFrame "#".
    iIntros ([w w']) "#Hww".
    iIntros (j K) "Hj /=".
    iDestruct "Hvv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iDestruct "Hww" as (m) "[% %]"; simplify_eq.
    iApply wp_atomic; eauto.
    iInv (logN .@ (l,l')) as ([v v']) "[Hv1 [>Hv2 #>Hv]]" "Hclose".
    iDestruct "Hv" as (?) "[% %]"; simplify_eq/=.
    iModIntro.
    iApply (wp_FAA with "Hv1"); auto using to_of_val.
    iNext. iIntros "Hw2".
    iMod (step_faa with "[$]") as "[Hu Hv2]"; eauto; first solve_ndisj.
    iMod ("Hclose" with "[Hw2 Hv2]").
    { iNext; iExists (#nv _, #nv _); simpl; iFrame. by eauto. }
    iModIntro.
    iExists (#nv _); iFrame; eauto.
  Qed.

  Theorem binary_fundamental Γ e τ :
    Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e ≤log≤ e : τ.
  Proof.
    induction 1.
    - iApply bin_log_related_var; done.
    - iApply bin_log_related_unit.
    - iApply bin_log_related_nat.
    - iApply bin_log_related_bool.
    - iApply bin_log_related_nat_binop; done.
    - iApply bin_log_related_pair; done.
    - iApply bin_log_related_fst; done.
    - iApply bin_log_related_snd; done.
    - iApply bin_log_related_injl; done.
    - iApply bin_log_related_injr; done.
    - iApply bin_log_related_case; done.
    - iApply bin_log_related_if; done.
    - iApply bin_log_related_rec; done.
    - iApply bin_log_related_lam; done.
    - iApply bin_log_related_letin; done.
    - iApply bin_log_related_seq; done.
    - iApply bin_log_related_app; done.
    - iApply bin_log_related_tlam; done.
    - iApply bin_log_related_tapp; done.
    - iApply bin_log_related_pack; done.
    - iApply bin_log_related_unpack; done.
    - iApply bin_log_related_fold; done.
    - iApply bin_log_related_unfold; done.
    - iApply bin_log_related_fork; done.
    - iApply bin_log_related_alloc; done.
    - iApply bin_log_related_load; done.
    - iApply bin_log_related_store; done.
    - iApply bin_log_related_CAS; done.
    - iApply bin_log_related_FAA; done.
  Qed.
End fundamental.
