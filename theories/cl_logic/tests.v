From iris.proofmode Require Import proofmode.
From iris_examples.cl_logic Require Import bi.

Section cl_logic_tests.
  Implicit Types P Q R : clProp.

  Lemma test_everything_persistent P : P -∗ P.
  Proof. by iIntros "#HP". Qed.

  Lemma test_everything_affine P : P -∗ True.
  Proof. by iIntros "_". Qed.

  Lemma test_iIntro_impl P Q R : ⊢ P → Q ∧ R → P ∧ R.
  Proof. iIntros "#HP #[HQ HR]". auto. Qed.

  Lemma test_iApply_impl_1 P Q R : ⊢ P → (P → Q) → Q.
  Proof. iIntros "HP HPQ". by iApply "HPQ". Qed.

  Lemma test_iApply_impl_2 P Q R : ⊢ P → (P → Q) → Q.
  Proof. iIntros "#HP #HPQ". by iApply "HPQ". Qed.

  Lemma test_excluded_middle P Q : ⊢ P ∨ ¬P.
  Proof.
    iApply clProp.dn; iIntros "#H". iApply "H".
    iRight. iIntros "HP". iApply "H". auto.
  Qed.

  Lemma test_peirces_law P Q : ((P → Q) → P) ⊢ P.
  Proof.
    iIntros "#H". iApply clProp.dn; iIntros "#HnotP". iApply "HnotP".
    iApply "H". iIntros "HP". iDestruct ("HnotP" with "HP") as %[].
  Qed.
End cl_logic_tests.
