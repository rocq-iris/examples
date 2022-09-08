(** A TaDA-style logically atomic specification for a freeable lock, derived for
    an arbitrary implementation of the freeable lock interface.

    In essence, this is an instance of the general fact that 'invariant-based'
    ("HoCAP-style") logically atomic specifications are equivalent to TaDA-style
    logically atomic specifications; see
    <https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/logatom/elimination_stack/hocap_spec.v>
    for that being worked out and explained in more detail for a stack specification.
*)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var ghost_map saved_prop.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation.
From iris_examples.locks Require Import freeable_lock.
From iris.prelude Require Import options.

(* TODO move to std++ *)
Section theorems.
Context `{FinMap K M}.

Lemma map_fold_delete {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  m !! i = Some x →
  R (map_fold f b m) (f i x (map_fold f b (delete i m))).
Proof using Type*.
  intros Hf_proper Hf Hi.
  rewrite <-map_fold_insert; [|done|done| |].
  - rewrite insert_delete; done.
  - intros j1 j2 ????. rewrite insert_delete_insert. auto.
  - rewrite lookup_delete. done.
Qed.

Lemma map_fold_delete_L {A B} (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  m !! i = Some x →
  map_fold f b m = f i x (map_fold f b (delete i m)).
Proof using Type*. apply map_fold_delete; apply _. Qed.

End theorems.

Inductive state := Free | Locked.

Class lockG Σ := LockG {
  lock_tokG : ghost_varG Σ state;
  lock_mapG : ghost_mapG Σ positive (frac * gname);
  lock_propG : savedPropG Σ;
}.
Local Existing Instances lock_tokG lock_mapG lock_propG.
Definition lockΣ : gFunctors := #[ghost_varΣ state; ghost_mapΣ positive (frac * gname); savedPropΣ].
Global Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section tada.
  Context `{!heapGS Σ, !lockG Σ} (l : freeable_lock) (N : namespace).

  Record tada_lock_name := TadaLockName {
    tada_lock_name_state : gname;
    tada_lock_name_map : gname;
    tada_lock_name_lock : l.(name);
  }.
  

  Definition tada_lock_state (γ : tada_lock_name) (s : state) : iProp Σ :=
    ghost_var γ.(tada_lock_name_state) (3/4) s ∗
    if s is Locked then
      l.(locked) γ.(tada_lock_name_lock) ∗ ghost_var γ.(tada_lock_name_state) (1/4) Locked
    else True.

  Local Definition acquire_AU γ (Q : iProp Σ) : iProp Σ :=
    AU << ∃∃ s : state, tada_lock_state γ s >>
       @ ⊤ ∖ ↑N, ∅
       << tada_lock_state γ Locked, COMM Q >>.

  Local Instance acquire_AU_proper γ :
    NonExpansive (acquire_AU γ).
  Proof.
    intros n ???. eapply atomic_update_ne.
    - solve_proper.
    - solve_proper.
    - intros [state ?] ?. rewrite /tele_app //=.
  Qed.

  Local Definition sum_loans (i : positive) (l : frac * gname) (state : frac) :=
    (l.1 + state)%Qp.

  Local Definition tada_lock_inv (γ : tada_lock_name) : iProp Σ :=
    (∃ q (loans : gmap positive (frac * gname)),
      l.(own_lock) γ.(tada_lock_name_lock) q ∗
      ghost_map_auth γ.(tada_lock_name_map) 1 loans ∗
      ⌜map_fold sum_loans q loans = 1%Qp⌝ ∗
      [∗ map] i ↦ l ∈ loans, ∃ Q, acquire_AU γ Q ∗ saved_prop_own l.2 DfracDiscarded Q) ∨
    (ghost_map_auth γ.(tada_lock_name_map) 1 ∅ ∗ ghost_var γ.(tada_lock_name_state) (3/4) Locked).

  Local Definition tada_lock_loan (γ : tada_lock_name) (q : frac) (Q : iProp Σ) : iProp Σ :=
    ∃ i γx, i ↪[γ.(tada_lock_name_map)] (q, γx) ∗ saved_prop_own γx DfracDiscarded Q.

  Definition tada_is_lock (γ : tada_lock_name) (lk : val) : iProp Σ :=
    l.(is_lock) γ.(tada_lock_name_lock) lk
      (ghost_var γ.(tada_lock_name_state) (1/4) Free) ∗
    inv N (tada_lock_inv γ).

  Global Instance tada_is_lock_persistent γ lk : Persistent (tada_is_lock γ lk).
  Proof. apply _. Qed.
  Global Instance tada_lock_state_timeless γ s : Timeless (tada_lock_state γ s).
  Proof. destruct s; apply _. Qed.

  Local Lemma tada_lock_state_exclusive' γ (s1 s2 : state) :
    tada_lock_state γ s1 -∗ ghost_var γ.(tada_lock_name_state) (3/4) s2 -∗ False.
  Proof.
    iIntros "[Hvar1 _] Hvar2".
    iDestruct (ghost_var_valid_2 with "Hvar1 Hvar2") as %[Hval _].
    exfalso. done.
  Qed.
  Lemma tada_lock_state_exclusive γ s1 s2 :
    tada_lock_state γ s1 -∗ tada_lock_state γ s2 -∗ False.
  Proof.
    iIntros "Hvar1 [Hvar2 _]". iApply (tada_lock_state_exclusive' with "Hvar1 Hvar2").
  Qed.

  Local Lemma sum_loans_assoc_comm (j1 j2 : positive) (z1 z2 : Qp * gname) (y : Qp) :
    sum_loans j1 z1 (sum_loans j2 z2 y) = sum_loans j2 z2 (sum_loans j1 z1 y).
  Proof.
    rewrite /sum_loans !assoc. f_equal. rewrite comm_L //.
  Qed.

  Local Lemma map_fold_sum_loans_add q1 q2 loans :
    (q1 + map_fold sum_loans q2 loans = map_fold sum_loans (q1+q2) loans)%Qp.
  Proof.
    revert q1. induction loans as [|???? IH] using map_ind; intros q1.
    { rewrite !map_fold_empty //. }
    rewrite map_fold_insert_L //.
    2:{ intros. apply sum_loans_assoc_comm. }
    rewrite map_fold_insert_L //.
    2:{ intros. apply sum_loans_assoc_comm. }
    rewrite {1 3}/sum_loans -IH.
    rewrite !assoc. f_equal. rewrite comm_L //.
  Qed.

  Local Lemma register_lock_acquire γ Q :
    inv N (tada_lock_inv γ) -∗
    acquire_AU γ Q -∗
    |={⊤}=> ∃ q, l.(own_lock) γ.(tada_lock_name_lock) q ∗ tada_lock_loan γ q Q.
  Proof.
    iIntros "#Hinv AU".
    iInv N as "[Hloans|>[_ Hdead]]"; last first.
    { iMod "AU" as (s) "[Hstate _]".
      iDestruct (tada_lock_state_exclusive' with "Hstate Hdead") as %[]. }
    iDestruct "Hloans" as (q loans) "(>Hown & >Hloanmap & >%Hq & Hloans)".
    set (i := fresh (dom loans)).
    assert (loans !! i = None).
    { apply not_elem_of_dom. apply is_fresh. }
    iMod (saved_prop_alloc Q DfracDiscarded) as (γx) "#HQ"; first done.
    iMod (ghost_map_insert i (q/2, γx)%Qp with "Hloanmap") as "[Hloadmap Hi]"; first done.
    iDestruct (own_lock_halves with "Hown") as "[Hown1 Hown2]".
    iModIntro. iSplitR "Hi Hown2".
    { (* Re-establish invariant *)
      iNext. iLeft. iExists (q/2)%Qp, _. iFrame. iSplit.
      - iPureIntro. rewrite map_fold_insert_L //.
        2:{ intros. apply sum_loans_assoc_comm. }
        rewrite {1}/sum_loans /= map_fold_sum_loans_add Qp.div_2. done.
      - iApply big_sepM_insert; first done. iFrame "Hloans".
        iExists _. by iFrame. }
    iModIntro. iExists _. iFrame.
    iExists _, _. by iFrame.
  Qed.

  Local Lemma return_lock_loan γ q Q :
    inv N (tada_lock_inv γ) -∗
    l.(own_lock) γ.(tada_lock_name_lock) q -∗
    tada_lock_loan γ q Q -∗
    |={⊤}=> ▷ ▷ acquire_AU γ Q.
  Proof.
    iIntros "#Hinv Hown (%i & %γx & Hi & #HQ)".
    iInv N as "[Hloans|>[Hdead _]]"; last first.
    { iDestruct (ghost_map_lookup with "Hdead Hi") as %Hi.
      rewrite lookup_empty in Hi. done. }
    iDestruct "Hloans" as (q0 loans) "(>Hown2 & >Hloanmap & >%Hq0 & Hloans)".
    iDestruct (ghost_map_lookup with "Hloanmap Hi") as %Hi.
    iMod (ghost_map_delete with "Hloanmap Hi") as "Hloanmap".
    iDestruct (big_sepM_delete _ _ i with "Hloans") as "[Hi Hloans]"; first done.
    iModIntro. iSplitR "Hi".
    { (* Re-establish invariant *)
      iNext. iLeft. iExists (q + q0)%Qp, _. iFrame "Hloanmap Hloans".
      iSplitL "Hown Hown2".
      { iApply own_lock_split. iFrame. }
      iPureIntro. move: Hq0. erewrite map_fold_delete_L.
      3: exact Hi.
      2: { intros. apply sum_loans_assoc_comm. }
      intros <-. rewrite {2}/sum_loans /=.
      rewrite map_fold_sum_loans_add. done.
    }
    do 2 iModIntro. iDestruct "Hi" as (Q') "[AU HQ']".
    iDestruct (saved_prop_agree with "HQ HQ'") as "EQ".
    iNext. iRewrite "EQ". done.
  Qed.    

  Lemma newlock_tada_spec :
    {{{ True }}}
      l.(newlock) #()
    {{{ lk γ, RET lk; tada_is_lock γ lk ∗ tada_lock_state γ Locked }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iMod (ghost_var_alloc Locked) as (γvar) "Hvar".
    replace 1%Qp with (3/4 + 1/4)%Qp; last first.
    { rewrite Qp.three_quarter_quarter //. }
    iDestruct "Hvar" as "[Hvar1 Hvar2]".
    iApply wp_fupd.
    wp_apply (l.(newlock_spec) with "[//]").
    iIntros (lk γlock) "(#Hlock & Hlocked & Hown)".
    iMod (ghost_map_alloc ∅) as (γmap) "[Hloanmap _]".
    set (γ := TadaLockName γvar γmap γlock).
    iMod (inv_alloc _ _ (tada_lock_inv γ) with "[Hown Hloanmap]").
    { iNext. iLeft. iExists 1%Qp, _. iFrame. iSplit.
      - iPureIntro. rewrite map_fold_empty. done.
      - rewrite big_sepM_empty. done. }
    iApply ("HΦ" $! lk γ).
    rewrite /tada_is_lock. iFrame. simpl. done.
  Qed.

  Lemma acquire_tada_spec γ lk :
    tada_is_lock γ lk -∗
    £2 -∗
    <<< ∀∀ s, tada_lock_state γ s >>>
      l.(acquire) lk @ ↑N
    <<< tada_lock_state γ Locked, RET #() >>>.
  Proof.
    iIntros "[#Hislock #Hinv] [Hlc1 Hlc2] %Φ AU".
    iMod (register_lock_acquire with "Hinv AU") as (q) "[Hown Hloan]".
    iApply wp_fupd.
    wp_apply (l.(acquire_spec) with "[$Hislock $Hown]").
    iIntros "(Hlocked & Hown & Hvar1)".
    iMod (return_lock_loan with "Hinv Hown Hloan") as "AU".
    iApply (lc_fupd_add_later with "Hlc1"). iNext.
    iApply (lc_fupd_add_later with "Hlc2"). iNext.
    iMod "AU" as (s) "[[Hvar2 _] [_ Hclose]]".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iMod (ghost_var_update_2 Locked with "Hvar1 Hvar2") as "[Hvar1 Hvar2]".
    { rewrite Qp.quarter_three_quarter //. }
    iMod ("Hclose" with "[$Hvar2 $Hlocked $Hvar1]"). done.
  Qed.

  Lemma release_tada_spec γ lk :
    tada_is_lock γ lk -∗
    <<< tada_lock_state γ Locked >>>
      l.(release) lk @ ↑N
    <<< tada_lock_state γ Free, RET #() >>>.
  Proof.
    iIntros "[#Hislock _] %Φ AU". iApply fupd_wp.
    iMod "AU" as "[[Hvar1 [Hlocked Hvar2]] [_ Hclose]]".
    iMod (ghost_var_update_2 Free with "Hvar1 Hvar2") as "[Hvar1 Hvar2]".
    { rewrite Qp.three_quarter_quarter //. }
    iMod ("Hclose" with "[$Hvar1]"). iModIntro.
    wp_apply (l.(release_spec) with "[$Hislock $Hlocked $Hvar2]").
    auto.
  Qed.

  Lemma freelock_tada_spec γ lk :
    tada_is_lock γ lk -∗
    {{{ £1 ∗ tada_lock_state γ Locked }}}
      l.(freelock) lk
    {{{ RET #(); True }}}.
  Proof.
    iIntros "[#Hislock #Hinv] !# %Φ [Hlc Hvar] HΦ".
    iApply fupd_wp. iInv N as "[Hloan|>[_ Hdead]]"; last first.
    { iDestruct (tada_lock_state_exclusive' with "Hvar Hdead") as %[]. }
    iApply (lc_fupd_add_later with "Hlc"). iNext.
    iDestruct "Hloan" as (q loans) "(Hown & Hloanmap & %Hq & Hloans)".
    destruct (decide (loans = ∅)) as [->|Hne]; last first.
    { (* loans non-empty: contradiction. *)
      apply map_choose in Hne as [i [x Hi]].
      iDestruct (big_sepM_lookup with "Hloans") as (Q) "[AU _]"; first by exact Hi.
      iMod "AU" as (st) "[Hst _]".
      iDestruct (tada_lock_state_exclusive with "Hvar Hst") as %[]. }
    iClear "Hloans". rewrite map_fold_empty in Hq. subst q.
    iModIntro. iDestruct "Hvar" as "(Hvar1 & Hlocked & _)". iSplitL "Hvar1 Hloanmap".
    { rewrite /tada_lock_inv. eauto with iFrame. }
    iModIntro.
    wp_apply (l.(freelock_spec) with "[$Hislock $Hlocked $Hown]").
    done.
  Qed.

End tada.

Global Typeclasses Opaque tada_is_lock tada_lock_state.
