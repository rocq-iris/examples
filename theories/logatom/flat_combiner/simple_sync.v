(* Coarse-grained syncer *)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import frac.
From iris_examples.logatom.flat_combiner Require Import sync.
From iris.prelude Require Import options.
Import uPred.

Local Existing Instance spin_lock.

Definition mk_sync: val :=
  λ: <>,
       let: "l" := newlock #() in
       λ: "f" "x",
          acquire "l";;
          let: "ret" := "f" "x" in
          release "l";;
          "ret".

Section syncer.
  Context `{!heapGS Σ, !lockG Σ}.
  
  Lemma mk_sync_spec: mk_syncer_spec mk_sync.
  Proof using Type*.
    iIntros (R Φ) "HR HΦ".
    wp_lam. wp_bind (newlock _).
    iApply (newlock_spec R with "[HR]"); first done. iNext.
    iIntros (lk γ) "#Hl". wp_pures. iApply "HΦ". iIntros "!#".
    iIntros (f) "!>". wp_pures.
    iIntros "!> !>" (P Q x) "#Hf !>". iIntros (Φ') "HP HΦ'".
    wp_pures. wp_bind (acquire _).
    iApply (acquire_spec with "Hl"). iNext.
    iIntros "[Hlocked R]". wp_seq. wp_bind (f _).
    iApply ("Hf" with "[$R $HP //]"). iNext.
    iIntros (v') "[HR HQv]". wp_let. wp_bind (release _).
    iApply (release_spec with "[$Hl $HR $Hlocked]").
    iNext. iIntros "_". wp_seq. iApply "HΦ'". done.
  Qed.
End syncer.
