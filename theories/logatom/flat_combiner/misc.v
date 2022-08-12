(* Miscellaneous lemmas *)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import excl auth frac gmap agree.
From iris.bi Require Import fractional.
From iris.prelude Require Import options.

Import uPred.

Section lemmas.
  Lemma pair_l_frac_op' (p q: Qp) (g g': val):
     ((p + q)%Qp, to_agree g') ~~> (((p, to_agree g') ⋅ (q, to_agree g'))).
  Proof. by rewrite -pair_op agree_idemp frac_op. Qed.

  Lemma pair_l_frac_op_1' (g g': val):
     (1%Qp, to_agree g') ~~> (((1/2)%Qp, to_agree g') ⋅ ((1/2)%Qp, to_agree g')).
  Proof. by rewrite -pair_op agree_idemp frac_op Qp.div_2. Qed.
  
End lemmas.

Section excl.
  Context `{!inG Σ (exclR unitO)}.
  Lemma excl_falso γ Q':
    own γ (Excl ()) ∗ own γ (Excl ()) ⊢ Q'.
  Proof.
    iIntros "[Ho1 Ho2]". iCombine "Ho1" "Ho2" as "Ho".
    iExFalso. by iDestruct (own_valid with "Ho") as "%".
  Qed.
End excl.

Section big_op_later.
  Context {M : ucmra}.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → uPred M. 

  Lemma big_sepM_delete_later Φ m i x :
    m !! i = Some x →
    ▷ ([∗ map] k↦y ∈ m, Φ k y) ⊣⊢ ▷ Φ i x ∗ ▷ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. intros ?. rewrite big_sepM_delete=>//. apply later_sep. Qed.

  Lemma big_sepM_insert_later Φ m i x :
    m !! i = None →
    ▷ ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ ▷ Φ i x ∗ ▷ [∗ map] k↦y ∈ m, Φ k y.
  Proof. intros ?. rewrite big_sepM_insert=>//. apply later_sep. Qed.
End big_op_later.

Section pair.
  Context {A : ofe} `{EqDecision A, !OfeDiscrete A, !LeibnizEquiv A, !inG Σ (prodR fracR (agreeR A))}.

  Lemma m_frag_agree γm (q1 q2: Qp) (a1 a2: A):
    own γm (q1, to_agree a1) -∗ own γm (q2, to_agree a2) -∗ ⌜a1 = a2⌝.
  Proof using Type*.
    iIntros "Ho Ho'".
    destruct (decide (a1 = a2)) as [->|Hneq]=>//.
    iCombine "Ho" "Ho'" as "Ho".
    iDestruct (own_valid with "Ho") as %Hvalid.
    exfalso. destruct Hvalid as [_ Hvalid].
    simpl in Hvalid. apply agree_op_inv in Hvalid. apply (inj to_agree) in Hvalid.
    apply Hneq. by fold_leibniz.
  Qed.
  
  Lemma m_frag_agree' γm (q1 q2: Qp) (a1 a2: A):
    own γm (q1, to_agree a1) -∗ own γm (q2, to_agree a2)
    -∗ own γm ((q1 + q2)%Qp, to_agree a1) ∗ ⌜a1 = a2⌝.
  Proof using Type*.
    iIntros "Ho Ho'".
    iDestruct (m_frag_agree with "Ho Ho'") as %Heq.
    subst. iCombine "Ho" "Ho'" as "Ho".
    by iFrame.
  Qed.
End pair.
