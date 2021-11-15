From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Import invariants lib.saved_prop.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth gset.
From iris_examples.barrier Require Export barrier.
From iris.prelude Require Import options.

(** The CMRAs/functors we need. *)
Class barrierG Σ := BarrierG {
  barrier_inG :> inG Σ (authR (gset_disjUR gname));
  barrier_savedPropG :> savedPropG Σ;
}.
Definition barrierΣ : gFunctors :=
  #[ GFunctor (authRF (gset_disjUR gname)); savedPropΣ ].

Global Instance subG_barrierΣ {Σ} : subG barrierΣ Σ → barrierG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!heapGS Σ, !barrierG Σ} (N : namespace).

Definition barrier_inv (l : loc) (γ : gname) (P : iProp Σ) : iProp Σ :=
  (∃ (b : bool) (γsps : gset gname),
    l ↦ #b ∗
    own γ (● (GSet γsps)) ∗
    ((if b then True else P) -∗
      ([∗ set] γsp ∈ γsps, ∃ R, saved_prop_own γsp R ∗ ▷ R)))%I.

Definition recv (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ γ P R' γsp,
    inv N (barrier_inv l γ P) ∗
    ▷ (R' -∗ R) ∗
    own γ (◯ GSet {[ γsp ]}) ∗
    saved_prop_own γsp R')%I.

Definition send (l : loc) (P : iProp Σ) : iProp Σ :=
  (∃ γ, inv N (barrier_inv l γ P))%I.

(** Setoids *)
Local Instance barrier_inv_ne l γ : NonExpansive (barrier_inv l γ).
Proof. solve_proper. Qed.
Global Instance send_ne l : NonExpansive (send l).
Proof. solve_proper. Qed.
Global Instance recv_ne l : NonExpansive (recv l).
Proof. solve_proper. Qed.

(** Actual proofs *)
Lemma newbarrier_spec (P : iProp Σ) :
  {{{ True }}} newbarrier #() {{{ l, RET #l; recv l P ∗ send l P }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam. wp_alloc l as "Hl".
  iApply ("HΦ" with "[> -]").
  iMod (saved_prop_alloc P) as (γsp) "#Hsp".
  iMod (own_alloc (● GSet {[ γsp ]} ⋅ ◯ GSet {[ γsp ]})) as (γ) "[H● H◯]".
  { by apply auth_both_valid_discrete. }
  iMod (inv_alloc N _ (barrier_inv l γ P) with "[Hl H●]") as "#Hinv".
  { iExists false, {[ γsp ]}. iIntros "{$Hl $H●} !> HP".
    rewrite big_sepS_singleton; eauto. }
  iModIntro; iSplitL "H◯".
  - iExists γ, P, P, γsp. iFrame; auto.
  - by iExists γ.
Qed.

Lemma signal_spec l P :
  {{{ send l P ∗ P }}} signal #l {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[Hs HP] HΦ". iDestruct "Hs" as (γ) "#Hinv". wp_lam.
  iInv N as ([] γsps) "(>Hl & H● & HRs)".
  { wp_store. iModIntro. iSplitR "HΦ"; last by iApply "HΦ".
    iExists true, γsps. iFrame. }
  wp_store. iDestruct ("HRs" with "HP") as "HRs".
  iModIntro. iSplitR "HΦ"; last by iApply "HΦ".
  iExists true, γsps. iFrame; eauto.
Qed.

Lemma wait_spec l P:
  {{{ recv l P }}} wait #l {{{ RET #(); P }}}.
Proof.
  rename P into R.
  iIntros (Φ) "HR HΦ". iDestruct "HR" as (γ P R' γsp) "(#Hinv & HR & H◯ & #Hsp)".
  iLöb as "IH". wp_rec. wp_bind (! _)%E.
  iInv N as ([] γsps) "(>Hl & >H● & HRs)"; last first.
  { wp_load. iModIntro. iSplitL "Hl H● HRs".
    { iExists false, γsps. iFrame. }
    wp_pures. by wp_apply ("IH" with "[$] [$]"). }
  iSpecialize ("HRs" with "[//]"). wp_load.
  iDestruct (own_valid_2 with "H● H◯")
    as %[Hvalid%gset_disj_included%elem_of_subseteq_singleton _]%auth_both_valid_discrete.
  iDestruct (big_sepS_delete with "HRs") as "[HR'' HRs]"; first done.
  iDestruct "HR''" as (R'') "[#Hsp' HR'']".
  iDestruct (saved_prop_agree with "Hsp Hsp'") as "#Heq".
  iMod (own_update_2 with "H● H◯") as "H●".
  { apply (auth_update_dealloc _ _ (GSet (γsps ∖ {[ γsp ]}))).
    apply gset_disj_dealloc_local_update. }
  iIntros "!>". iSplitL "Hl H● HRs".
  { iDestruct (bi.later_intro with "HRs") as "HRs".
    iModIntro. iExists true, (γsps ∖ {[ γsp ]}). iFrame; eauto. }
  wp_if. iApply "HΦ". iApply "HR". by iRewrite "Heq".
Qed.

Lemma recv_split E l P1 P2 :
  ↑N ⊆ E → recv l (P1 ∗ P2) ={E}=∗ recv l P1 ∗ recv l P2.
Proof.
  rename P1 into R1; rename P2 into R2.
  iIntros (?). iDestruct 1 as (γ P R' γsp) "(#Hinv & HR & H◯ & #Hsp)".
  iInv N as (b γsps) "(>Hl & >H● & HRs)".
  iDestruct (own_valid_2 with "H● H◯")
    as %[Hvalid%gset_disj_included%elem_of_subseteq_singleton _]%auth_both_valid_discrete.
  iMod (own_update_2 with "H● H◯") as "H●".
  { apply (auth_update_dealloc _ _ (GSet (γsps ∖ {[ γsp ]}))).
    apply gset_disj_dealloc_local_update. }
  set (γsps' := γsps ∖ {[γsp]}).
  iMod (saved_prop_alloc_cofinite γsps' R1) as (γsp1 Hγsp1) "#Hsp1".
  iMod (saved_prop_alloc_cofinite (γsps' ∪ {[ γsp1 ]}) R2)
    as (γsp2 [? ?%not_elem_of_singleton_1]%not_elem_of_union) "#Hsp2".
  iMod (own_update _ _ (● _ ⋅ (◯ GSet {[ γsp1 ]} ⋅ ◯ (GSet {[ γsp2 ]})))
    with "H●") as "(H● & H◯1 & H◯2)".
  { rewrite -auth_frag_op gset_disj_union; last set_solver.
    apply auth_update_alloc, (gset_disj_alloc_empty_local_update _ {[ γsp1; γsp2 ]}).
    set_solver. }
  iModIntro. iSplitL "HR Hl HRs H●".
  { iModIntro. iExists b, ({[γsp1; γsp2]} ∪ γsps').
    iIntros "{$Hl $H●} HP". iSpecialize ("HRs" with "HP").
    iDestruct (big_sepS_delete with "HRs") as "[HR'' HRs]"; first done.
    iDestruct "HR''" as (R'') "[#Hsp' HR'']".
    iDestruct (saved_prop_agree with "Hsp Hsp'") as "#Heq".
    iAssert (▷ R')%I with "[HR'']" as "HR'"; [iNext; by iRewrite "Heq"|].
    iDestruct ("HR" with "HR'") as "[HR1 HR2]".
    iApply big_sepS_union; first set_solver. iFrame "HRs".
    iApply big_sepS_union; first set_solver.
    iSplitL "HR1"; rewrite big_sepS_singleton; eauto. }
  iModIntro; iSplitL "H◯1".
  - iExists γ, P, R1, γsp1. iFrame; auto.
  - iExists γ, P, R2, γsp2. iFrame; auto.
Qed.

Lemma recv_weaken l P1 P2 : (P1 -∗ P2) -∗ recv l P1 -∗ recv l P2.
Proof.
  iIntros "HP". iDestruct 1 as (γ P R' i) "(#Hinv & HR & H◯)".
  iExists γ, P, R', i. iIntros "{$Hinv $H◯} !> HQ". iApply "HP". by iApply "HR".
Qed.

Lemma recv_mono l P1 P2 : (P1 ⊢ P2) → recv l P1 ⊢ recv l P2.
Proof. iIntros (HP) "H". iApply (recv_weaken with "[] H"). iApply HP. Qed.
End proof.

Typeclasses Opaque send recv.
