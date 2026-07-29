From iris.algebra Require Import excl frac.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris_examples.locks Require Import freeable_lock.

Definition newlock : val := λ: <>, ref #true.
Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Definition release : val := λ: "l", "l" <- #false.
Definition freelock : val := λ: "l", Free "l".

(** The CMRA we need. *)
(* Not bundling heapGS, as it may be shared with other users. *)
Class lockG Σ := LockG {
  lock_tokG : inG Σ (exclR unitO);
  lock_ownG : inG Σ fracR;
}.
Local Existing Instances lock_tokG lock_ownG.

Definition lockΣ : gFunctors := #[GFunctor (exclR unitO); GFunctor fracR].

Global Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Record spin_lock_name := {
  spin_lock_name_locked : gname;
  spin_lock_name_own : gname;
}.

Section proof.
  Context `{!heapGS_gen hlc Σ, !lockG Σ}.
  Let N := nroot .@ "spin_lock".

  Local Definition lock_inv (γ : spin_lock_name) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ.(spin_lock_name_locked) (Excl ()) ∗ R) ∨
    (own γ.(spin_lock_name_locked) (Excl ()) ∗ own γ.(spin_lock_name_own) 1%Qp).

  Definition is_lock (γ : spin_lock_name) (lk : val) (R : iProp Σ) : iProp Σ :=
    ∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv γ l R).

  Definition locked (γ : spin_lock_name) : iProp Σ :=
    own γ.(spin_lock_name_locked) (Excl ()).

  Definition own_lock (γ : spin_lock_name) (q : frac) : iProp Σ :=
    own γ.(spin_lock_name_own) q.

  Lemma locked_exclusive (γ : spin_lock_name) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

  Lemma own_lock_valid (γ : spin_lock_name) q :
    own_lock γ q -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    iIntros "Hown". iDestruct (own_valid with "Hown") as %?. done.
  Qed.

  Lemma own_lock_split (γ : spin_lock_name) q1 q2 :
    own_lock γ (q1+q2) ⊣⊢ own_lock γ q1 ∗ own_lock γ q2.
  Proof. rewrite /own_lock own_op //. Qed.

  Global Instance lock_inv_ne γ l : NonExpansive (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_contractive γ l : Contractive (is_lock γ l).
  Proof. solve_contractive. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent γ l R : Persistent (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.
  Global Instance own_lock_timeless γ q : Timeless (own_lock γ q).
  Proof. apply _. Qed.

  Lemma is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ↔ R2) -∗ is_lock γ lk R2.
  Proof.
    iDestruct 1 as (l ->) "#Hinv"; iIntros "#HR".
    iExists l; iSplit; [done|]. iApply (inv_iff with "Hinv").
    iIntros "!> !>"; iSplit.
    all: iDestruct 1 as "[(%b & Hl & H)|H]"; last by iRight.
    all: iLeft; iExists b; iFrame "Hl"; destruct b;
      first [done|iDestruct "H" as "[$ ?]"; by iApply "HR"].
  Qed.

  Lemma newlock_spec (R : iProp Σ):
    {{{ True }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R ∗ locked γ ∗ own_lock γ 1 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /newlock /=.
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γlocked) "Hlocked"; first done.
    iMod (own_alloc 1%Qp) as (γown) "Hown"; first done.
    set (γ := Build_spin_lock_name γlocked γown).
    iMod (inv_alloc N _ (lock_inv γ l R) with "[Hl]") as "#?".
    { iIntros "!>". iLeft. iExists true. by iFrame. }
    iModIntro. iApply ("HΦ" $! _ γ). iFrame. iExists _. eauto.
  Qed.

  Lemma try_acquire_spec γ lk q R :
    {{{ is_lock γ lk R ∗ own_lock γ q }}}
      try_acquire lk
    {{{ b, RET #b; if b is true then locked γ ∗ own_lock γ q ∗ R else own_lock γ q }}}.
  Proof.
    iIntros (Φ) "[#Hl Hown] HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (CmpXchg _ _ _). iInv N as "[Hlock|>[_ Hcancel]]"; last first.
    { rewrite /own_lock. iCombine "Hown Hcancel" gives %Hc.
      rewrite frac_op frac_valid in Hc. exfalso. eapply Qp.not_add_le_r. done. }
    iDestruct "Hlock" as ([]) "[Hl HR]".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl"; first (iNext; iLeft; iExists true; eauto).
      wp_pures. iApply ("HΦ" $! false). done.
    - wp_cmpxchg_suc. iDestruct "HR" as "[Hγ HR]".
      iModIntro. iSplitL "Hl"; first (iNext; iLeft; iExists true; eauto).
      rewrite /locked. wp_pures. by iApply ("HΦ" $! true with "[$Hγ $HR $Hown]").
  Qed.

  Lemma acquire_spec γ lk q R :
    {{{ is_lock γ lk R ∗ own_lock γ q }}}
      acquire lk
    {{{ RET #(); locked γ ∗ own_lock γ q ∗ R }}}.
  Proof.
    iIntros (Φ) "[#Hl Hown] HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "[$Hl $Hown]"). iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; auto with iFrame.
    - iIntros "Hown". wp_if. iApply ("IH" with "Hown [HΦ]"). auto.
  Qed.

  Lemma release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /release /=. wp_lam. iInv N as "[Hlock|>[Hcancel _]]"; last first.
    { iDestruct (locked_exclusive with "Hlocked Hcancel") as %[]. }
    iDestruct "Hlock" as (b) "[Hl _]".
    wp_store. iSplitR "HΦ"; last by iApply "HΦ".
    iModIntro. iNext. iLeft. iExists false. by iFrame.
  Qed.

  Lemma freelock_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ own_lock γ 1 }}}
      freelock lk
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#Hlock & Hlocked & Hown) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    wp_lam. iInv N as "[Hlock|>[Hcancel _]]"; last first.
    { iDestruct (locked_exclusive with "Hlocked Hcancel") as %[]. }
    iDestruct "Hlock" as (b) "[Hl _]".
    wp_free. iSplitR "HΦ"; last by iApply "HΦ".
    iModIntro. iNext. iRight. iFrame.
  Qed.
End proof.

Global Typeclasses Opaque is_lock own_lock locked.

Canonical Structure freeablespin_lock `{!heapGS_gen hlc Σ, !lockG Σ} : freeable_lock :=
  {| freeable_lock.locked_exclusive := locked_exclusive;
     freeable_lock.is_lock_iff := is_lock_iff;
     freeable_lock.own_lock_split := own_lock_split;
     freeable_lock.own_lock_valid := own_lock_valid;
     freeable_lock.newlock_spec := newlock_spec;
     freeable_lock.acquire_spec := acquire_spec;
     freeable_lock.release_spec := release_spec;
     freeable_lock.freelock_spec := freelock_spec;
  |}.
