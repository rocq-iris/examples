From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Export nondet_bool.
From iris_examples.proph Require Import eager_coin_spec.
From iris_examples.proph.lib Require Import one_shot_proph.

(* Lazy implementation of the eager specification. The value of the coin is
unknown at the time of the creation of the coin. As a consequence, we rely on
a *one-shot* prophecy variable. *)

Definition new_lazy_coin : val :=
  λ: <>, (ref NONE, NewProph).

Definition read_lazy_coin : val :=
  λ: "cp",
  let: "c" := Fst "cp" in
  let: "p" := Snd "cp" in
  match: !"c" with
    NONE => let: "r" := nondet_bool #() in
           "c" <- SOME "r";; resolve_proph: "p" to: "r";; "r"
  | SOME "b" => "b"
  end.

Section proof.
  Context `{!heapGS Σ}.

  Definition val_to_bool (v : val) : bool := bool_decide (v = #true).

  Lemma val_to_bool_of_bool (b : bool) :
    val_to_bool #b = b.
  Proof.
    by destruct b.
  Qed.

  Definition lazy_coin (cp : val) (b : bool) : iProp Σ :=
    (∃ (c : loc) (p : proph_id) (v : val),
        ⌜cp = (#c, #p)%V⌝ ∗
        (c ↦ SOMEV #b ∨ (c ↦ NONEV ∗ proph1 p v ∗ ⌜b = val_to_bool v⌝)))%I.

  Lemma lazy_coin_exclusive (cp : val) (b1 b2 : bool) :
    lazy_coin cp b1 -∗ lazy_coin cp b2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (c1 p1 v1) "[-> H1]".
    iDestruct "H2" as (c2 p2 v2) "[% H2]".
    simplify_eq.
    iDestruct "H1" as "[Hc1 | [Hc1 _]]";
    iDestruct "H2" as "[Hc2 | [Hc2 _]]";
    by iCombine "Hc1 Hc2" gives %[??].
  Qed.

  Lemma new_lazy_coin_spec :
    {{{ True }}}
      new_lazy_coin #()
    {{{ c b, RET c; lazy_coin c b }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply wp_new_proph1; first done. iIntros (p v) "Hp".
    wp_alloc c as "Hc". wp_pair. iModIntro.
    iApply ("HΦ" $! (#c, #p)%V).
    iExists c, p, v. iSplit; first done. iRight. by iFrame.
  Qed.

  Lemma read_lazy_coin_spec cp b :
    {{{ lazy_coin cp b }}}
      read_lazy_coin cp
    {{{ RET #b; lazy_coin cp b }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iDestruct "Hc" as (c p v ->) "[Hc | [Hc [Hp ->]]]".
    - wp_lam. wp_load. wp_match. iApply "HΦ". iModIntro.
      iExists c, p, #(). iSplit; first done. by iLeft.
    - wp_lam. wp_load. wp_match.
      wp_apply nondet_bool_spec; first done. iIntros (r) "_".
      wp_let. wp_store.
      wp_apply (wp_resolve1 with "Hp"); first done.
      wp_pures. iIntros "!> ->". wp_pures.
      rewrite !val_to_bool_of_bool. iApply "HΦ". iModIntro.
      iExists c, p, #(). iSplit; first done. by iLeft.
  Qed.

End proof.

Definition lazy_coin_spec_instance `{!heapGS Σ} :
  eager_coin_spec.eager_coin_spec Σ :=
  {| eager_coin_spec.new_coin_spec := new_lazy_coin_spec;
     eager_coin_spec.read_coin_spec := read_lazy_coin_spec;
     eager_coin_spec.coin_exclusive := lazy_coin_exclusive |}.

Global Typeclasses Opaque lazy_coin.
