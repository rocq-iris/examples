(** Concurrent bag specification from the HOCAP paper.
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

Deriving the sequential specification from the abstract one
*)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris_examples.hocap Require Import abstract_bag.

Section proof.
  Context `{heapGS Σ}.
  Variable b : bag Σ.
  Variable N : namespace.

  (** An exclusive specification keeps track of the exact contents of the bag *)
  Definition bagE (γ : name Σ b) (x : val) (X : gmultiset val) : iProp Σ :=
    (is_bag b N γ x ∗ bag_contents b γ X)%I.

  Lemma newBag_spec :
    {{{ True }}}
      newBag b #()
    {{{ x, RET x; ∃ γ, bagE γ x ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply newBag_spec; eauto.
    iNext. iIntros (x γ) "[#Hbag Hb]". iApply "HΦ".
    iExists γ; by iFrame.
  Qed.

  Lemma pushBag_spec γ x X v :
    {{{ bagE γ x X }}}
       pushBag b x (of_val v)
    {{{ RET #(); bagE γ x ({[+ v +]} ⊎ X) }}}.
  Proof.
    iIntros (Φ) "Hbag HΦ".
    iApply (pushBag_spec b N (bagE γ x X)%I (bagE γ x ({[+ v +]} ⊎ X))%I γ with "[] [Hbag]"); eauto.
    { iModIntro. iIntros (Y) "[Hb1 Hb2]".
      iDestruct "Hb2" as "[#Hbag Hb2]".
      iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
      iMod (bag_contents_update b ({[+ v +]} ⊎ Y) with "[$Hb1 $Hb2]") as "[Hb1 Hb2]".
      by iFrame. }
    { iDestruct "Hbag" as "[#Hbag Hb]". iFrame "Hbag". eauto. }
  Qed.

  Lemma popBag_spec γ x X :
    {{{ bagE γ x X }}}
       popBag b x
    {{{ v, RET v; (⌜X = ∅⌝ ∧ ⌜v = NONEV⌝ ∧ bagE γ x ∅)
                 ∨ (∃ Y y, ⌜X = {[+ y +]} ⊎ Y⌝ ∧ ⌜v = SOMEV y⌝ ∧ bagE γ x Y)}}}.
  Proof.
    iIntros (Φ) "Hbag HΦ".
    iApply (popBag_spec b N (bagE γ x X)%I (fun v => (⌜X = ∅⌝ ∧ ⌜v = NONEV⌝ ∧ bagE γ x ∅)
                 ∨ (∃ Y y, ⌜X = {[+ y +]} ⊎ Y⌝ ∧ ⌜v = SOMEV y⌝ ∧ bagE γ x Y))%I γ with "[] [] [Hbag]"); eauto.
    { iModIntro. iIntros (Y y) "[Hb1 Hb2]".
      iDestruct "Hb2" as "[#Hbag Hb2]".
      iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
      iMod (bag_contents_update b Y with "[$Hb1 $Hb2]") as "[Hb1 Hb2]".
      iFrame. iRight. iModIntro. iExists _,_; repeat iSplit; eauto. }
    { iModIntro. iIntros "[Hb1 Hb2]".
      iDestruct "Hb2" as "[#Hbag Hb2]".
      iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
      iModIntro. iFrame. iLeft. repeat iSplit; eauto. }
    { iDestruct "Hbag" as "[#Hbag Hb]". iFrame "Hbag". eauto. }
  Qed.
End proof.

