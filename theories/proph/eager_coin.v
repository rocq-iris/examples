From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Export nondet_bool.
From iris_examples.proph Require Import eager_coin_spec.
From iris.prelude Require Import options.

(* Simple implementation of the eager specification. *)

Definition new_eager_coin : val :=
  λ: <>, ref (nondet_bool #()).

Definition read_eager_coin : val :=
  λ: "c", !"c".

Section proof.
  Context `{!heapGS Σ}.

  Definition eager_coin (c : val) (b : bool) : iProp Σ :=
    (∃ (l : loc), ⌜c = #l⌝ ∗ l ↦ #b).

  Lemma eager_coin_exclusive (c : val) (b1 b2 : bool) :
    eager_coin c b1 -∗ eager_coin c b2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (l1) "[% Hl1]".
    iDestruct "H2" as (l2) "[% Hl2]".
    simplify_eq.
    by iDestruct (mapsto_valid_2 with "Hl1 Hl2") as %[??].
  Qed.

  Lemma new_eager_coin_spec :
    {{{ True }}}
      new_eager_coin #()
    {{{ c b, RET c; eager_coin c b }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_apply nondet_bool_spec; first done.
    iIntros (r) "_". wp_alloc l as "Hl". iApply "HΦ". iExists l. by iFrame.
  Qed.

  Lemma read_eager_coin_spec c b :
    {{{ eager_coin c b }}}
      read_eager_coin c
    {{{ RET #b; eager_coin c b }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iDestruct "Hc" as (l) "[-> Hl]".
    wp_lam. wp_load. iApply "HΦ". iExists l. by iFrame.
  Qed.
End proof.

Definition eager_coin_spec_instance `{!heapGS Σ} :
  eager_coin_spec.eager_coin_spec Σ :=
  {| eager_coin_spec.new_coin_spec := new_eager_coin_spec;
     eager_coin_spec.read_coin_spec := read_eager_coin_spec;
     eager_coin_spec.coin_exclusive := eager_coin_exclusive |}.

Global Typeclasses Opaque eager_coin.
