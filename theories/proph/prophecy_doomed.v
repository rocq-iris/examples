From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris_examples.proph Require Import one_shot_proph.
From iris.prelude Require Import options.

(** This demonstrates the common pattern of knowing that an execution is
"doomed" due to a clearly incorrect prophecy, but still having to play along and
work with the bogus data in the proof until the prophecy is resolved. *)

Definition prediction: val :=
  λ: <>,
    let: "p" := NewProph in
    resolve_proph: "p" to: #42;;
    #().

Section proof.
  Context `{!heapGS Σ}.

  (** Defines when this is a well-formed prediction. *)
  Definition prophecy_wf (v : val) : Prop :=
    v = #42.

  Lemma prediction_spec :
    {{{ True }}} prediction #() {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply wp_new_proph1; first done.
    iIntros (p v) "Hp".
    destruct (decide (prophecy_wf v)) as [Hwf|Hdoomed].
    - (* Case 1: Well-formed prediction, all is good. *)
      wp_smart_apply (wp_resolve_proph1 with "Hp").
      iIntros "_". wp_pures. iApply "HΦ". done.
    - (* Case 2: The prediction is doomed, as proven by [Hdoomed]. At this point
         we *know* we will be able to prove [False] when the prophecy will be
         resolved, but we still have to complete the proof until then. In this
         example, the resolution is the next thing that happens; in a real
         proof, the code will do "stuff" before the resolution and we have to
         still complete the proof of all that "stuff". *)
      wp_smart_apply (wp_resolve_proph1 with "Hp").
      iIntros "%Hproof".
      (* Now with [Hdoomed] and [Hproof] we can derive a contradiction. *)
      exfalso. apply Hdoomed. rewrite /prophecy_wf.
      rewrite Hproof. done.
  Qed.
End proof.
