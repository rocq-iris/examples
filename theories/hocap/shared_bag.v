(** Concurrent bag specification from the HOCAP paper.
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

Deriving the concurrent specification from the abstract one
*)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris_examples.hocap Require Import abstract_bag.
From iris.prelude Require Import options.

Section proof.
  Context `{heapGS Σ}.
  Variable b : bag Σ.
  Variable N : namespace.
  Definition NB := N.@"bag".
  Definition NI := N.@"inv".
  (** Predicate that will be satisfied by all the elements in the bag.
      The first argument is the bag itself. *)
  Variable P : val → val → iProp Σ.

  Definition bagS_inv (γ : name Σ b) (y : val) : iProp Σ :=
    inv NI (∃ X, bag_contents b γ X ∗ [∗ mset] x ∈ X, P y x)%I.
  Definition bagS (γ : name Σ b) (x : val) : iProp Σ :=
    (is_bag b NB γ x ∗ bagS_inv γ x)%I.

  Global Instance bagS_persistent γ x : Persistent (bagS γ x).
  Proof. apply _. Qed.

  Lemma newBag_spec :
    {{{ True }}}
      newBag b #()
    {{{ x, RET x; ∃ γ, bagS γ x }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd.
    iApply (newBag_spec b NB); eauto.
    iNext. iIntros (v γ) "[#Hbag Hcntn]".
    iMod (inv_alloc NI _ (∃ X, bag_contents b γ X ∗ [∗ mset] x ∈ X, P v x)%I with "[Hcntn]") as "#Hinv".
    { iNext. iExists _. iFrame. by rewrite big_sepMS_empty. }
    iApply "HΦ". iModIntro. iExists _; by iFrame "Hinv".
  Qed.

  Lemma pushBag_spec γ x v :
    {{{ bagS γ x ∗ P x v }}}
       pushBag b x (of_val v)
    {{{ RET #(); bagS γ x }}}.
  Proof.
    iIntros (Φ) "[#[Hbag Hinv] HP] HΦ". rewrite /bagS_inv.
    iApply (pushBag_spec b NB (P x v)%I (True)%I with "[] [Hbag HP]"); eauto.
    { iModIntro. iIntros (Y) "[Hb1 HP]".
      iInv NI as (X) "[>Hb2 HPs]" "Hcl".
      iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
      iMod (bag_contents_update b ({[+ v +]} ⊎ Y) with "[$Hb1 $Hb2]") as "[Hb1 Hb2]".
      iFrame. iApply "Hcl".
      iNext. iExists _; iFrame.
      rewrite big_sepMS_singleton. iFrame. }
    { iNext. iIntros "_". iApply "HΦ". by iFrame "Hinv". }
  Qed.

  Lemma popBag_spec γ x :
    {{{ bagS γ x }}}
       popBag b x
    {{{ v, RET v; bagS γ x ∗ (⌜v = NONEV⌝ ∨ (∃ y, ⌜v = SOMEV y⌝ ∧ P x y)) }}}.
  Proof.
    iIntros (Φ) "[#Hbag #Hinv] HΦ".
    iApply (popBag_spec b NB (True)%I (fun v => (⌜v = NONEV⌝ ∨ (∃ y, ⌜v = SOMEV y⌝ ∧ P x y)))%I with "[] [] [Hbag]"); eauto.
    { iModIntro. iIntros (Y y) "[Hb1 _]".
      iInv NI as (X) "[>Hb2 HPs]" "Hcl".
      iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
      iMod (bag_contents_update b Y with "[$Hb1 $Hb2]") as "[Hb1 Hb2]".
      rewrite big_sepMS_disj_union bi.later_sep big_sepMS_singleton.
      iDestruct "HPs" as "[HP HPs]".
      iMod ("Hcl" with "[-HP Hb1]") as "_".
      { iNext. iExists _; iFrame. }
      iModIntro. iNext. iFrame. iRight; eauto. }
    { iModIntro. iIntros "[Hb1 _]".
      iModIntro. iNext. iFrame. iLeft; eauto. }
    { iNext. iIntros (v) "H". iApply "HΦ". iFrame "Hinv Hbag H". }
  Qed.

End proof.
