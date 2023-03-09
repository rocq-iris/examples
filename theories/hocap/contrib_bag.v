(** Bag with contributions specification *)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmultiset frac_auth.
From iris_examples.hocap Require Import abstract_bag.
From iris.prelude Require Import options.

Section proof.
  Context `{heapGS Σ}.
  Variable b : bag Σ.
  Variable N : namespace.
  Definition NB := N.@"bag".
  Definition NI := N.@"inv".

  Context `{inG Σ (frac_authR (gmultisetUR val))}.

  Definition bagM_inv (γb : name Σ b) (γ : gname) : iProp Σ :=
    inv NI (∃ X, bag_contents b γb X ∗ own γ (●F X))%I.
  Definition bagM (γb : name Σ b) (γ : gname) (x : val) : iProp Σ :=
    (is_bag b NB γb x ∗ bagM_inv γb γ)%I.
  Definition bagPart (γ : gname) (q : Qp) (X : gmultiset val) : iProp Σ :=
    (own γ (◯F{q} X))%I.

  Lemma bagPart_compose (γ: gname) (q1 q2: Qp) (X Y : gmultiset val) :
    bagPart γ q1 X -∗ bagPart γ q2 Y -∗ bagPart γ (q1+q2) (X ⊎ Y).
  Proof.
    iIntros "Hp1 Hp2".
    rewrite /bagPart -gmultiset_op -frac_op.
    rewrite frac_auth_frag_op own_op. iFrame.
  Qed.
  Lemma bagPart_decompose (γ: gname) (q: Qp) (X Y : gmultiset val) :
    bagPart γ q (X ⊎ Y) -∗ bagPart γ (q/2) X ∗ bagPart γ (q/2) Y.
  Proof.
    iIntros "Hp".
    assert (q = (q/2)+(q/2))%Qp as Hq by (by rewrite Qp.div_2).
    rewrite /bagPart {1}Hq.
    rewrite -gmultiset_op -frac_op.
    rewrite frac_auth_frag_op own_op. iFrame.
  Qed.

  Global Instance bagM_persistent γb γ x : Persistent (bagM γb γ x).
  Proof. apply _. Qed.

  Lemma newBag_spec :
    {{{ True }}}
      newBag b #()
    {{{ x, RET x; ∃ γb γ, bagM γb γ x ∗ bagPart γ 1 ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd.
    iApply (newBag_spec b NB); eauto.
    iNext. iIntros (v γb) "[#Hbag Hcntn]".
    iMod (own_alloc (●F ∅ ⋅ ◯F ∅)) as (γ) "[Hown Hpart]"; first by apply auth_both_valid_discrete.
    iMod (inv_alloc NI _ (∃ X, bag_contents b γb X ∗ own γ (●F X))%I with "[Hcntn Hown]") as "#Hinv".
    { iNext. iExists _. iFrame. }
    iApply "HΦ". iModIntro. iExists _,_. iFrame "Hinv Hbag Hpart".
  Qed.

  Lemma pushBag_spec γb γ x v q Y :
    {{{ bagM γb γ x ∗ bagPart γ q Y }}}
       pushBag b x (of_val v)
    {{{ RET #(); bagPart γ q ({[+ v +]} ⊎ Y) }}}.
  Proof.
    iIntros (Φ) "[#[Hbag Hinv] HP] HΦ". rewrite /bagM_inv.
    iApply (pushBag_spec b NB (bagPart γ q Y)%I (bagPart γ q ({[+ v +]} ⊎ Y))%I with "[] [Hbag HP]"); eauto.
    iModIntro. iIntros (X) "[Hb1 HP]".
    iInv NI as (X') "[>Hb2 >Hown]" "Hcl".
    iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
    iMod (bag_contents_update b ({[+ v +]} ⊎ X) with "[$Hb1 $Hb2]") as "[Hb1 Hb2]".
    rewrite /bagPart.
    iMod (own_update_2 with "Hown HP") as "[Hown HP]".
    { apply (frac_auth_update _ _ _ ({[+ v +]} ⊎ X) ({[+ v +]} ⊎ Y)).
      do 2 rewrite (comm _ {[+ v +]}).
      apply gmultiset_local_update_alloc. }
    iFrame. iApply "Hcl".
    iNext. iExists _; iFrame.
  Qed.

  Local Ltac multiset_solver :=
    intro;
    repeat (rewrite multiplicity_difference || rewrite multiplicity_disj_union);
    (lia || naive_solver).

  Lemma popBag_spec γb γ x X :
    {{{ bagM γb γ x ∗ bagPart γ 1 X }}}
       popBag b x
    {{{ v, RET v;
        (⌜v = NONEV⌝ ∧ ⌜X = ∅⌝ ∗ bagPart γ 1 X)
       ∨ (∃ y, ⌜v = SOMEV y⌝ ∧ ⌜y ∈ X⌝ ∗ bagPart γ 1 (X ∖ {[+ y +]})) }}}.
  Proof.
    iIntros (Φ) "[[#Hbag #Hinv] Hpart] HΦ".
    iApply (popBag_spec b NB (bagPart γ 1 X)%I
             (fun v => (⌜v = NONEV⌝ ∧ ⌜X = ∅⌝ ∗ bagPart γ 1 X)
                     ∨ (∃ y, ⌜v = SOMEV y⌝ ∧ ⌜y ∈ X⌝ ∗ bagPart γ 1 (X ∖ {[+ y +]})))%I with "[] [] [Hpart]"); eauto.
    { iModIntro. iIntros (Y y) "[Hb1 Hpart]".
      iInv NI as (X') "[>Hb2 >HPs]" "Hcl".
      iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
      iMod (bag_contents_update b Y with "[$Hb1 $Hb2]") as "[Hb1 Hb2]".
      rewrite /bagPart.
      iAssert (⌜X = ({[+ y +]} ⊎ Y)⌝)%I with "[Hpart HPs]" as %->.
      { iCombine "HPs Hpart" gives %Hfoo.
        apply frac_auth_agree in Hfoo. by unfold_leibniz. }
      iMod (own_update_2 with "HPs Hpart") as "Hown".
      { apply (frac_auth_update _ _ _ (({[+ y +]} ⊎ Y) ∖ {[+ y +]}) (({[+ y +]} ⊎ Y) ∖ {[+ y +]})).
        apply gmultiset_local_update_dealloc; multiset_solver. }
      iDestruct "Hown" as "[HPs Hpart]".
      iMod ("Hcl" with "[-Hpart Hb1]") as "_".
      { iNext. iExists _; iFrame.
        assert (Y = (({[+ y +]} ⊎ Y) ∖ {[+ y +]})) as <-
          by (unfold_leibniz; multiset_solver).
        iFrame. }
      iModIntro. iNext. iFrame. iRight. iExists y; repeat iSplit; eauto.
      iPureIntro. apply gmultiset_elem_of_disj_union. left.
      by apply gmultiset_elem_of_singleton. }
    { iModIntro. iIntros "[Hb1 Hpart]".
      iInv NI as (X') "[>Hb2 >HPs]" "Hcl".
      iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
      iAssert (⌜X = ∅⌝)%I with "[Hpart HPs]" as %->.
      { rewrite /bagPart.
        iCombine "HPs Hpart" gives %Hfoo.
        apply frac_auth_agree in Hfoo. by unfold_leibniz. }
      iMod ("Hcl" with "[Hb2 HPs]") as "_".
      { iNext. iExists _; iFrame. }
      iModIntro. iNext. iFrame. iLeft; eauto. }
  Qed.

End proof.
