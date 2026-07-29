From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Export nondet_bool.
From iris_examples.proph.lib Require Import typed_proph.
From iris_examples.proph Require Import clairvoyant_coin_spec.

(* Clairvoyant coin with *typed* prophecies. *)

Definition new_coin: val :=
  λ: <>, (ref (nondet_bool #()), NewProph).

Definition read_coin : val := λ: "cp", !(Fst "cp").

Definition toss_coin : val :=
  λ: "cp",
  let: "c" := Fst "cp" in
  let: "p" := Snd "cp" in
  let: "r" := nondet_bool #() in
  "c" <- "r";; resolve_proph: "p" to: "r";; #().

Section proof.
  Context `{!heapGS Σ}.

  Definition coin (cp : val) (bs : list bool) : iProp Σ :=
    (∃ (c : loc) (p : proph_id) (b : bool) (bs' : list bool),
        ⌜cp = (#c, #p)%V⌝ ∗ ⌜bs = b :: bs'⌝ ∗ c ↦ #b ∗
          (typed_proph_prop BoolTypedProph) p bs')%I.

  Lemma coin_exclusive (cp : val) (bs1 bs2 : list bool) :
    coin cp bs1 -∗ coin cp bs2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (c1 p1 b1 bs'1) "(-> & -> & _ & Hp1)".
    iDestruct "H2" as (c2 p2 b2 bs'2) "(% & -> & _ & Hp2)".
    simplify_eq.
    iApply (typed_proph_prop_excl BoolTypedProph). iFrame.
  Qed.

  Lemma new_coin_spec :
    {{{ True }}}
      new_coin #()
    {{{ c bs, RET c; coin c bs }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply (typed_proph_wp_new_proph BoolTypedProph); first done.
    iIntros (bs p) "Hp".
    wp_apply nondet_bool_spec; first done.
    iIntros (b) "_". wp_alloc c as "Hc". wp_pair.
    iApply ("HΦ" $! _ (b :: bs)).
    iExists c, p, b, bs. by iFrame.
  Qed.

  Lemma read_coin_spec cp bs :
    {{{ coin cp bs }}}
      read_coin cp
    {{{ b bs', RET #b; ⌜bs = b :: bs'⌝ ∗ coin cp bs }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iDestruct "Hc" as (c p b bs') "[-> [-> [Hc Hp]]]".
    wp_lam. wp_load. iApply "HΦ". iModIntro. iSplit; first done.
    iExists c, p, b, bs'. by iFrame.
  Qed.

  Lemma toss_coin_spec cp bs :
    {{{ coin cp bs }}}
      toss_coin cp
    {{{ b bs', RET #(); ⌜bs = b :: bs'⌝ ∗ coin cp bs' }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iDestruct "Hc" as (c p b bs') "[-> [-> [Hc Hp]]]".
    wp_lam. wp_pures. wp_apply nondet_bool_spec; first done.
    iIntros (r) "_". wp_store.
    wp_apply (typed_proph_wp_resolve BoolTypedProph with "[Hp]"); try done.
    wp_pures. iIntros "!>" (bs) "-> Hp". wp_seq.
    iModIntro. iApply "HΦ"; iSplit; first done.
    iExists c, p, r, bs. by iFrame.
  Qed.

End proof.

Definition clairvoyant_coin_spec_instance `{!heapGS Σ} :
  clairvoyant_coin_spec.clairvoyant_coin_spec Σ :=
  {| clairvoyant_coin_spec.new_coin_spec := new_coin_spec;
     clairvoyant_coin_spec.read_coin_spec := read_coin_spec;
     clairvoyant_coin_spec.toss_coin_spec := toss_coin_spec;
     clairvoyant_coin_spec.coin_exclusive := coin_exclusive |}.

Global Typeclasses Opaque coin.
