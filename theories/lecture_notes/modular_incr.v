(* Modular Specifications for Concurrent Modules. *)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import agree frac frac_auth.
From iris.prelude Require Import options.

From iris.bi.lib Require Import fractional.

From iris.heap_lang.lib Require Import par.

Definition cntCmra : cmra := prodR fracR (agreeR ZO).

Class cntG Σ := CntG { CntG_inG :: inG Σ cntCmra }.
Definition cntΣ : gFunctors := #[GFunctor cntCmra ].

Global Instance subG_cntΣ {Σ} : subG cntΣ Σ → cntG Σ.
Proof. solve_inG. Qed.

Definition newcounter : val :=
  λ: "m", ref "m".

Definition read : val := λ: "ℓ", !"ℓ".

Definition incr: val :=
  rec: "incr" "l" :=
     let: "oldv" := !"l" in
     if: CAS "l" "oldv" ("oldv" + #1)
       then "oldv" (* return old value if success *)
       else "incr" "l".

Definition wk_incr : val :=
    λ: "l", let: "n" := !"l" in
            "l" <- "n" + #1.

Section cnt_model.
  Context `{!cntG Σ}.

  Definition makeElem (q : Qp) (m : Z) : cntCmra := (q, to_agree m).
  Typeclasses Opaque makeElem.

  Notation "γ ⤇[ q ] m" := (own γ (makeElem q m))
    (at level 20, q at level 50, format "γ ⤇[ q ]  m") : bi_scope.
  Notation "γ ⤇½ m" := (own γ (makeElem (1/2) m))
    (at level 20, format "γ ⤇½  m") : bi_scope.

  Global Instance makeElem_fractional γ m: Fractional (λ q, γ ⤇[q] m)%I.
  Proof.
    intros p q. rewrite /makeElem.
    rewrite -own_op; f_equiv.
    split; first done.
    by rewrite /= agree_idemp.
  Qed.

  Global Instance makeElem_as_fractional γ m q:
    AsFractional (own γ (makeElem q m)) (λ q, γ ⤇[q] m)%I q.
  Proof.
    split; first done. apply _.
  Qed.

  Global Instance makeElem_Exclusive m: Exclusive (makeElem 1 m).
  Proof.
    rewrite /makeElem. intros [y ?] [H _]. apply (exclusive_l _ _ H).
  Qed.

  Lemma makeElem_op p q n:
    makeElem p n ⋅ makeElem q n ≡ makeElem (p + q) n.
  Proof.
    rewrite /makeElem; split; first done.
    by rewrite /= agree_idemp.
  Qed.

  Lemma makeElem_eq γ p q (n m : Z):
    γ ⤇[p] n -∗ γ ⤇[q] m -∗ ⌜n = m⌝.
  Proof.
    iIntros "H1 H2".
    iCombine "H1 H2" gives %HValid.
    destruct HValid as [_ H2].
    iIntros "!%"; by apply to_agree_op_inv_L.
  Qed.

  Lemma makeElem_entail γ p q (n m : Z):
    γ ⤇[p] n -∗ γ ⤇[q] m -∗ γ ⤇[p + q] n.
  Proof.
    iIntros "H1 H2".
    iDestruct (makeElem_eq with "H1 H2") as %->.
    iCombine "H1" "H2" as "H". done.
  Qed.

  Lemma makeElem_update γ (n m k : Z):
    γ ⤇½ n -∗ γ ⤇½ m ==∗ γ ⤇[1] k.
  Proof.
    iIntros "H1 H2".
    iDestruct (makeElem_entail with "H1 H2") as "H".
    rewrite Qp.div_2.
    iApply (own_update with "H"); by apply cmra_update_exclusive.
  Qed.
End cnt_model.

Notation "γ ⤇[ q ] m" := (own γ (makeElem q m))
  (at level 20, q at level 50, format "γ ⤇[ q ]  m") : bi_scope.
Notation "γ ⤇½ m" := (own γ (makeElem (1/2) m))
  (at level 20, format "γ ⤇½  m") : bi_scope.

Section cnt_spec.
  Context `{!heapGS Σ, !cntG Σ} (N : namespace).

  Definition cnt_inv ℓ γ := (∃ (m : Z), ℓ ↦ #m ∗ γ ⤇½ m)%I.

  Definition Cnt (ℓ : loc) (γ : gname) : iProp Σ :=
    inv (N .@ "internal") (cnt_inv ℓ γ).

  Lemma Cnt_alloc (E : coPset) (m : Z) (ℓ : loc):
    (ℓ ↦ #m) ={E}=∗ ∃ γ, Cnt ℓ γ ∗ γ ⤇½ m.
  Proof.
    iIntros "Hpt".
    iMod (own_alloc (makeElem 1 m)) as (γ) "[Hown1 Hown2]"; first done.
    iMod (inv_alloc (N.@ "internal") _ (cnt_inv ℓ γ)%I with "[Hpt Hown1]") as "#HInc".
    { iExists _; iFrame. }
    iModIntro; iExists _; iFrame "# Hown2".
  Qed.

  Theorem newcounter_spec (E : coPset) (m : Z):
    ↑(N .@ "internal") ⊆ E →
    {{{ True }}} newcounter #m @ E {{{ (ℓ : loc), RET #ℓ; ∃ γ, Cnt ℓ γ ∗ γ ⤇½ m}}}.
  Proof.
    iIntros (Hsubset Φ) "#Ht HΦ".
    wp_lam.
    wp_alloc ℓ as "Hl".
    iApply "HΦ".
    by iApply Cnt_alloc.
  Qed.

  Theorem read_spec (γ : gname) (E : coPset) (P : iProp Σ) (Q : Z → iProp Σ) (ℓ : loc):
    ↑(N .@ "internal") ⊆ E →
    (∀ m, □ (γ ⤇½ m ∗ P ={E ∖ ↑(N .@ "internal")}=∗ γ ⤇½ m ∗ Q m)) ⊢
    {{{ Cnt ℓ γ ∗ P}}} read #ℓ @ E {{{ (m : Z), RET #m; Cnt ℓ γ ∗ Q m }}}.
  Proof.
    iIntros (Hsubset) "#HVS".
    iIntros (Φ) "!# [#HInc HP] HCont".
    wp_rec.
    rewrite /Cnt.
    iInv (N .@ "internal") as (m) "[>Hpt >Hown]" "HClose".
    iMod ("HVS" $! m with "[Hown HP]") as "[Hown HQ]"; first by iFrame.
    wp_load.
    iMod ("HClose" with "[Hpt Hown]") as "_".
    { iNext; iExists _; iFrame. }
    iApply "HCont".
    iModIntro.
    iFrame.
    done.
  Qed.

  Theorem incr_spec (γ : gname) (E : coPset) (P : iProp Σ) (Q : Z → iProp Σ) (ℓ : loc):
    ↑(N .@ "internal") ⊆ E →
    (∀ (n : Z), □ (γ ⤇½ n ∗ P  ={E ∖ ↑(N .@ "internal")}=∗ γ ⤇½ (n+1) ∗ Q n)) ⊢
    {{{ Cnt ℓ γ ∗ P }}} incr #ℓ @ E {{{ (m : Z), RET #m; Cnt ℓ γ ∗ Q m}}}.
  Proof.
    iIntros (Hsubset) "#HVS".
    iIntros (Φ) "!# [#HInc HP] HCont".
    iLöb as "IH".
    wp_rec.
    wp_bind (! _)%E.
    iInv (N .@ "internal") as (m) "[>Hpt >Hown]" "HClose".
    wp_load.
    iMod ("HClose" with "[Hpt Hown]") as "_".
    { iNext; iExists _; iFrame. }
    iModIntro.
    wp_let.
    wp_op.
    wp_bind (CmpXchg _ _ _)%E.
    iInv (N .@ "internal") as (m') "[>Hpt >Hown]" "HClose".
    destruct (decide (m = m')); simplify_eq.
    - wp_cmpxchg_suc.
      iMod ("HVS" $! m' with "[Hown HP]") as "[Hown HQ]"; first iFrame.
      iMod ("HClose" with "[Hpt Hown]") as "_".
      { iNext; iExists _; iFrame. }
      iModIntro.
      wp_pures.
      iApply "HCont"; by iFrame.
    - wp_cmpxchg_fail.
      iMod ("HClose" with "[Hpt Hown]") as "_".
      { iNext; iExists _; iFrame. }
      iModIntro.
      wp_pures.
      iApply ("IH" with "HP HCont").
  Qed.

  Theorem wk_incr_spec (γ : gname) (E : coPset) (P Q : iProp Σ) (ℓ : loc) (n : Z) (q : Qp):
    ↑(N .@ "internal") ⊆ E →
    □ (γ ⤇½ n ∗ γ ⤇[q] n ∗ P ={E ∖ ↑(N .@ "internal")}=∗ γ ⤇½ (n+1) ∗ Q) -∗
    {{{ Cnt ℓ γ ∗ γ ⤇[q] n ∗ P}}} wk_incr #ℓ @ E {{{ RET #(); Cnt ℓ γ ∗ Q}}}.
  Proof.
    iIntros (Hsubset) "#HVS".
    iIntros (Φ) "!# [#HInc [Hγ HP]] HCont".
    wp_lam.
    wp_bind (! _)%E.
    iInv (N .@ "internal") as (m) "[>Hpt >Hown]" "HClose".
    wp_load.
    iDestruct (makeElem_eq with "Hγ Hown") as %->.
    iMod ("HClose" with "[Hpt Hown]") as "_".
    { iNext; iExists _; iFrame. }
    iModIntro.
    wp_let.
    wp_op.
    iInv (N .@ "internal") as (k) "[>Hpt >Hown]" "HClose".
    iDestruct (makeElem_eq with "Hγ Hown") as %->.
    iMod ("HVS" with "[$Hown $HP $Hγ]") as "[Hown HQ]".
    wp_store.
    iMod ("HClose" with "[Hpt Hown]") as "_".
    { iNext; iExists _; iFrame. }
    iModIntro.
    iApply "HCont"; by iFrame.
  Qed.

  Theorem wk_incr_spec' (γ : gname) (E : coPset) (P Q : iProp Σ) (ℓ : loc) (n : Z) (q : Qp):
    ↑(N .@ "internal") ⊆ E →
    □ (γ ⤇½ n ∗ γ ⤇[q] n ∗ P ={E ∖ ↑(N .@ "internal")}=∗ γ ⤇½ (n+1) ∗  γ ⤇[q] (n + 1) ∗ Q) -∗
    {{{ Cnt ℓ γ ∗ γ ⤇[q] n ∗ P}}} wk_incr #ℓ @ E {{{ RET #(); Cnt ℓ γ ∗  γ ⤇[q] (n + 1) ∗ Q}}}.
  Proof.
    iIntros (Hsubset) "#HVS".
    iApply wk_incr_spec; done.
Qed.

End cnt_spec.
Global Opaque newcounter incr read wk_incr.

Section incr_twice.
  Context `{!heapGS Σ, !cntG Σ} (N : namespace).
  Definition incr_twice : val := λ: "ℓ", incr "ℓ" ;; incr "ℓ".

  Theorem incr_twice_spec (γ : gname) (E : coPset) (P : iProp Σ) (Q Q' : Z → iProp Σ) (ℓ : loc):
    ↑(N .@ "internal") ⊆ E →
    (∀ (n : Z), □ (γ ⤇½ n ∗ P  ={E ∖ ↑(N .@ "internal")}=∗ γ ⤇½ (n+1) ∗ Q n))
      -∗
      (∀ (n : Z), □ (γ ⤇½ n ∗ (∃ m, Q m)  ={E ∖ ↑(N .@ "internal")}=∗ γ ⤇½ (n+1) ∗ Q' n))
      -∗
      {{{ Cnt N ℓ γ ∗ P }}} incr_twice #ℓ @ E {{{ (m : Z), RET #m; Cnt N ℓ γ ∗ Q' m}}}.
  Proof.
    iIntros (?) "#HVS1 #HVS2 !#".
    iIntros (Φ) "HPre HΦ".
    wp_lam. wp_bind (incr _)%E.
    wp_apply (incr_spec with "HVS1 HPre"); auto.
    iIntros (m) "[HCnt HPre]".
    wp_seq.
    wp_apply (incr_spec with "HVS2 [$HCnt HPre]"); auto.
  Qed.
End incr_twice.

Section example_1.
  Context `{!heapGS Σ, !spawnG Σ, !cntG Σ} (N : namespace).

  Definition incr_2 : val :=
    λ: "x",
       let: "l" := newcounter "x" in
       incr "l" ||| incr "l";;
       read "l".

  (* Prove that incr is safe w.r.t. data race. TODO: prove a stronger post-condition *)
  Lemma incr_2_safe:
    ∀ (x: Z), ⊢ WP incr_2 #x {{ _, True }}.
  Proof using Type* N.
    iIntros (x).
    rewrite /incr_2 /=.
    wp_lam.
    wp_bind (newcounter _)%E.
    wp_apply newcounter_spec; auto; iIntros (ℓ) "H".
    iDestruct "H" as (γ) "[#HInc Hown2]".
    iMod (inv_alloc (N.@ "external") _ (∃m, own γ (makeElem (1/2) m))%I with "[Hown2]") as "#Hinv".
    { iNext; iExists _; iFrame. }
    iDestruct (incr_spec N γ ⊤ True%I (λ _, True)%I with "[]") as "#HIncr"; eauto.
    { iIntros (n) "!# [Hown _]".
      iInv (N .@ "external") as (m) ">Hownm" "H2".
      iMod (makeElem_update _ _ _ (n + 1) with "Hown Hownm") as "[Hown Hown']".
      iMod ("H2" with "[Hown]") as "_".
      { iExists _; iFrame. }
      iModIntro; iFrame.
    }
    wp_let.
    wp_bind (_ ||| _)%E.
    let tac := iApply ("HIncr" with "[$HInc]"); iNext; by iIntros (?) "_" in
    wp_smart_apply (wp_par (λ _, True%I) (λ _, True%I)); [tac | tac | ].
    { iIntros (v1 v2) "_ !>".
      wp_seq.
      wp_apply (read_spec _ _ _ True%I (λ _, True%I)); auto.
    }
  Qed.
End example_1.
