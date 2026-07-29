From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode.
From iris_examples.barrier Require Export barrier.
From iris_examples.barrier Require Import proof.
Import uPred.

Section spec.
Local Set Default Proof Using "Type*".
Context `{!heapGS Σ, !barrierG Σ}.

Lemma barrier_spec (N : namespace) :
  ∃ recv send : loc → iPropO Σ -n> iPropO Σ,
    (∀ P, ⊢ {{{ True }}} newbarrier #()
                     {{{ (l : loc), RET #l; recv l P ∗ send l P }}}) ∧
    (∀ l P, ⊢ {{{ send l P ∗ P }}} signal #l {{{ RET #(); True }}}) ∧
    (∀ l P, ⊢ {{{ recv l P }}} wait #l {{{ RET #(); P }}}) ∧
    (∀ l P Q, recv l (P ∗ Q) ={↑N}=∗ recv l P ∗ recv l Q) ∧
    (∀ l P Q, (P -∗ Q) -∗ recv l P -∗ recv l Q).
Proof.
  exists (λ l, OfeMor (recv N l)), (λ l, OfeMor (send N l)).
  split_and?; simpl.
  - iIntros (P) "!#". iIntros (Φ). iApply (newbarrier_spec _ P).
  - iIntros (l P) "!#". iIntros (Φ). iApply signal_spec.
  - iIntros (l P) "!#". iIntros (Φ). iApply wait_spec.
  - iIntros (l P Q). by iApply recv_split.
  - apply recv_weaken.
Qed.
End spec.
