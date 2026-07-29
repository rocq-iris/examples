From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Export nondet_bool.
From iris_examples.proph Require Import clairvoyant_coin_spec.

(* Clairvoyant coin using (untyped) sequence prophecies. *)

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

  Definition prophecy_to_list_bool (vs : list (val * val)) : list bool :=
    (λ v, bool_decide (v = #true)) ∘ snd <$> vs.

  Definition coin (cp : val) (bs : list bool) : iProp Σ :=
    (∃ (c : loc) (p : proph_id) (vs : list (val * val)),
        ⌜cp = (#c, #p)%V⌝ ∗
        ⌜bs ≠ []⌝ ∗ ⌜tail bs = prophecy_to_list_bool vs⌝ ∗
        proph p vs ∗
        from_option (λ b : bool, c ↦ #b) (∃ b : bool, c ↦ #b) (head bs))%I.

  Lemma coin_exclusive (cp : val) (bs1 bs2 : list bool) :
    coin cp bs1 -∗ coin cp bs2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (c1 p1 vs1) "(-> & _ & _ & Hp1 & _)".
    iDestruct "H2" as (c2 p2 vs2) "(% & _ & _ & Hp2 & _)".
    simplify_eq. iApply (proph_exclusive with "Hp1 Hp2").
  Qed.

  Lemma new_coin_spec : {{{ True }}} new_coin #() {{{ c bs, RET c; coin c bs }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_apply wp_new_proph; first done.
    iIntros (vs p) "Hp".
    wp_apply nondet_bool_spec; first done.
    iIntros (b) "_".
    wp_alloc c as "Hc".
    wp_pair.
    iApply ("HΦ" $! (#c, #p)%V (b :: prophecy_to_list_bool vs)).
    rewrite /coin; eauto 10 with iFrame.
  Qed.

  Lemma read_coin_spec cp bs :
    {{{ coin cp bs }}}
      read_coin cp
    {{{ b bs', RET #b; ⌜bs = b :: bs'⌝ ∗ coin cp bs }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iDestruct "Hc" as (c p vs -> ? ?) "[Hp Hb]".
    destruct bs as [|b bs]; simplify_eq/=.
    wp_lam. wp_load.
    iModIntro. iApply "HΦ"; iSplit; first done.
    rewrite /coin; eauto 10 with iFrame.
  Qed.

  Lemma toss_coin_spec cp bs :
    {{{ coin cp bs }}}
      toss_coin cp
    {{{ b bs', RET #(); ⌜bs = b :: bs'⌝ ∗ coin cp bs' }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iDestruct "Hc" as (c p vs -> ? ?) "[Hp Hb]".
    destruct bs as [|b bs]; simplify_eq/=.
    wp_lam. do 2 (wp_proj; wp_let).
    wp_apply nondet_bool_spec; first done.
    iIntros (r) "_".
    wp_store.
    wp_apply (wp_resolve_proph with "[Hp]"); first done.
    iIntros (ws) "[-> Hp]".
    wp_seq. iModIntro.
    iApply "HΦ"; iSplit; first done.
    destruct r; rewrite /coin; eauto 10 with iFrame.
  Qed.

End proof.

Definition clairvoyant_coin_spec_instance `{!heapGS Σ} :
  clairvoyant_coin_spec.clairvoyant_coin_spec Σ :=
  {| clairvoyant_coin_spec.new_coin_spec := new_coin_spec;
     clairvoyant_coin_spec.read_coin_spec := read_coin_spec;
     clairvoyant_coin_spec.toss_coin_spec := toss_coin_spec;
     clairvoyant_coin_spec.coin_exclusive := coin_exclusive |}.

Global Typeclasses Opaque coin.
