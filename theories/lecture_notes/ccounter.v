(* Counter with contributions. A specification derived from the modular
   specification proved in modular_incr module. *)
From iris.base_logic Require Import invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import numbers frac_auth.
From iris.prelude Require Import options.

From iris_examples.lecture_notes Require Import modular_incr.

Class ccounterG Σ := CCounterG { ccounter_inG :> inG Σ (frac_authR natR) }.
Definition ccounterΣ : gFunctors := #[GFunctor (frac_authR natR)].

Global Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
Proof. solve_inG. Qed.

Section ccounter.
  Context `{!heapGS Σ, !cntG Σ, !ccounterG Σ} (N : namespace).

  Lemma ccounterRA_valid (m n : natR) (q : frac): ✓ (●F m ⋅ ◯F{q} n) → n ≤ m.
  Proof.
    intros ?.
    (* This property follows directly from the generic properties of the relevant RAs. *)
    apply nat_included. by apply: (frac_auth_included_total q).
  Qed.

  Lemma ccounterRA_valid_full (m n : natR): ✓ (●F m ⋅ ◯F n) → n = m.
  Proof.
    by intros ?%frac_auth_agree.
  Qed.

  Lemma ccounterRA_update (m n : natR) (q : frac): (●F m ⋅ ◯F{q} n) ~~> (●F (S m) ⋅ ◯F{q} (S n)).
  Proof.
    apply frac_auth_update, (nat_local_update _ _ (S _) (S _)).
    lia.
  Qed.

  Definition ccounter_inv (γ₁ γ₂ : gname): iProp Σ :=
    (∃ n, own γ₁ (●F n) ∗ γ₂ ⤇½ (Z.of_nat n))%I.

  Definition is_ccounter (γ₁ γ₂ : gname) (l : loc) (q : frac) (n : natR) : iProp Σ := (own γ₁ (◯F{q} n) ∗ inv (N .@ "counter") (ccounter_inv γ₁ γ₂)  ∗ Cnt N l γ₂)%I.

  (** The main proofs. *)
  Lemma is_ccounter_op γ₁ γ₂ ℓ q1 q2 (n1 n2 : nat) :
    is_ccounter γ₁ γ₂ ℓ (q1 + q2) (n1 + n2) ⊣⊢ is_ccounter γ₁ γ₂ ℓ q1 n1 ∗ is_ccounter γ₁ γ₂ ℓ q2 n2.
  Proof.
    apply bi.equiv_entails; split; rewrite /is_ccounter frac_auth_frag_op own_op.
    - iIntros "[? #?]".
      iFrame "#"; iFrame.
    - iIntros "[[? #?] [? _]]".
      iFrame "#"; iFrame.
  Qed.

  Lemma newcounter_contrib_spec (R : iProp Σ) m:
    {{{ True }}}
        newcounter #m
    {{{ γ₁ γ₂ ℓ, RET #ℓ; is_ccounter γ₁ γ₂ ℓ 1 m }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite -wp_fupd.
    wp_apply newcounter_spec; auto.
    iIntros (ℓ) "H"; iDestruct "H" as (γ₂) "[#HCnt Hown]".
    iMod (own_alloc (●F m ⋅ ◯F m)) as (γ₁) "[Hγ Hγ']"; first by apply auth_both_valid_discrete.
    iMod (inv_alloc (N .@ "counter") _ (ccounter_inv γ₁ γ₂) with "[Hγ Hown]").
    { iNext. iExists _. by iFrame. }
    iModIntro. iApply "HΦ". rewrite /is_ccounter; eauto.
  Qed.

  Lemma incr_contrib_spec γ₁ γ₂ ℓ q n :
    {{{ is_ccounter γ₁ γ₂ ℓ q n  }}}
        incr #ℓ
    {{{ (y : Z), RET #y; is_ccounter γ₁ γ₂ ℓ q (S n) }}}.
  Proof.
    iIntros (Φ) "[Hown #[Hinv HCnt]] HΦ".
    iApply (incr_spec N γ₂ _ (own γ₁ (◯F{q} n))%I (λ _, (own γ₁ (◯F{q} (S n))))%I with "[] [Hown]"); first set_solver.
    - iIntros (m) "!# [HOwnElem HP]".
      iInv (N .@ "counter") as (k) "[>H1 >H2]" "HClose".
      iDestruct (makeElem_eq with "HOwnElem H2") as %->.
      iMod (makeElem_update _ _ _ (k+1) with "HOwnElem H2") as "[HOwnElem H2]".
      iMod (own_update_2 with "H1 HP") as "[H1 HP]".
      { apply ccounterRA_update. }
      iMod ("HClose" with "[H1 H2]") as "_".
      { iNext; iExists (S k); iFrame.
        rewrite Nat2Z.inj_succ Z.add_1_r //.
      }
      by iFrame.
    - by iFrame.
    - iNext.
      iIntros (m) "[HCnt' Hown]".
      iApply "HΦ". by iFrame.
  Qed.

  Lemma read_contrib_spec γ₁ γ₂ ℓ q n :
    {{{ is_ccounter γ₁ γ₂ ℓ q n }}}
        read #ℓ
    {{{ (c : Z), RET #c; ⌜(Z.of_nat n ≤ c)%Z⌝ ∧ is_ccounter γ₁ γ₂ ℓ q n }}}.
  Proof.
    iIntros (Φ) "[Hown #[Hinv HCnt]] HΦ".
    wp_apply (read_spec N γ₂ _ (own γ₁ (◯F{q} n))%I (λ m,
        ⌜(n ≤ m)%Z⌝ ∗ (own γ₁ (◯F{q} n)))%I with "[] [Hown]"); first set_solver.
    - iIntros (m) "!# [HownE HOwnfrag]".
      iInv (N .@ "counter") as (k) "[>H1 >H2]" "HClose".
      iDestruct (makeElem_eq with "HownE H2") as %->.
      iCombine "H1 HOwnfrag" gives %Hleq%ccounterRA_valid.
      iMod ("HClose" with "[H1 H2]") as "_".
      { iExists _; by iFrame. }
      iFrame; iIntros "!>!%".
      auto using inj_le.
    - by iFrame.
    - iIntros (i) "[_ [% HQ]]".
      iApply "HΦ".
      iSplit; first by iIntros "!%".
      iFrame; iFrame "#".
  Qed.

  Lemma read_contrib_spec_1 γ₁ γ₂ ℓ n :
    {{{ is_ccounter γ₁ γ₂ ℓ 1%Qp n }}} read #ℓ
    {{{ RET #n; is_ccounter γ₁ γ₂ ℓ 1 n }}}.
  Proof.
    iIntros (Φ) "[Hown #[Hinv HCnt]] HΦ".
    wp_apply (read_spec N γ₂ _ (own γ₁ (◯F n))%I (λ m, ⌜Z.of_nat n = m⌝ ∗ (own γ₁ (◯F n)))%I with "[] [Hown]"); first set_solver.
    - iIntros (m) "!# [HownE HOwnfrag]".
      iInv (N .@ "counter") as (k) "[>H1 >H2]" "HClose".
      iDestruct (makeElem_eq with "HownE H2") as %->.
      iCombine "H1 HOwnfrag" gives %Hleq%ccounterRA_valid_full; simplify_eq.
      iMod ("HClose" with "[H1 H2]") as "_".
      { iExists _; by iFrame. }
      iFrame; by iIntros "!>!%".
    - by iFrame.
    - iIntros (i) "[_ [% HQ]]".
      simplify_eq. iApply "HΦ".
      iFrame; iFrame "#".
  Qed.
End ccounter.
