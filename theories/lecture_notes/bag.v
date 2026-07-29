(* This file contains Example 7.38 of the Iris Lecture Notes. We implement a
   concurrent course grained bag based on the lock in `lock.v`.
*)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import auth.

From iris_examples.lecture_notes Require Import lock.

Definition newbag : val :=
  λ: <>, let: "ℓ" := ref NONE in
         let: "v" := newlock #() in ("ℓ", "v").

Definition insert : val :=
  λ: "x" "e", let: "ℓ" := Fst "x" in
                  let: "lock" := Snd "x" in
                  acquire "lock" ;; 
                  "ℓ" <- SOME ("e", !"ℓ") ;;
                  release "lock".

Definition remove : val :=
  λ: "x", let: "ℓ" := Fst "x" in
          let: "lock" := Snd "x" in
          acquire "lock" ;; 
          let: "r" := !"ℓ" in 
          let: "res" := match: "r" with
                          NONE => NONE
                        | SOME "p" => "ℓ" <- Snd "p" ;; SOME (Fst "p")
                        end
          in release "lock" ;; "res".

Section spec.
  Context `{!heapGS Σ, lockG Σ}.
  Local Notation iProp := (iProp Σ).

  Fixpoint isBag (Ψ : val → iProp) (v : val) : iProp :=
    match v with
    | NONEV => ⌜True⌝%I
    | SOMEV (x, r) => (Ψ x ∗ isBag Ψ r)%I
    | _ => ⌜False⌝%I
    end.

  Definition is_bag (v : val) (Ψ : val → iProp) :=
    (∃ (ℓ : loc) (v₂ : val) γ, ⌜v = (#ℓ, v₂)%V⌝ ∗ is_lock γ v₂ (∃ u, ℓ ↦ u ∗ isBag Ψ u))%I.

  Global Instance bag_persistent v Ψ: Persistent (is_bag v Ψ).
  Proof. apply _. Qed.

  Lemma newbag_triple_spec Ψ:
    {{{ True }}} newbag #() {{{ b, RET b; is_bag b Ψ}}}.
  Proof.
    iIntros (ϕ) "_ Hcont".
    wp_lam ; wp_alloc ℓ as "Hℓ"; wp_let.
    wp_apply ((newlock_spec (∃ u, ℓ ↦ u ∗ isBag Ψ u))%I with "[Hℓ]").
    { iExists NONEV. auto. }
    iIntros (v). iDestruct 1 as (γ) "IL".
    wp_pures. iApply "Hcont".
    iExists ℓ, v, γ. iFrame. done.
  Qed.

  Lemma bag_insert_triple_spec v Ψ e: 
    {{{ is_bag v Ψ ∗ Ψ e }}} insert v e {{{ RET #(); True }}}.
  Proof.
    iIntros (ϕ) "[Hb Hψ] Hcont".
    iDestruct "Hb" as (ℓ u γ) "[% #IL]"; subst.
    wp_lam. wp_pures.
    wp_apply (acquire_spec with "IL"); first done.
    iIntros (v) "[P HLocked]".
    iDestruct "P" as (b) "[Hp Hb]".
    wp_load. wp_store.
    iApply (release_spec with "[$IL $HLocked Hp Hψ Hb]"); first done.
    { iExists _. iFrame "Hp". iFrame. }
    done.
  Qed.

  Lemma bag_remove_triple_spec v Ψ:
    {{{ is_bag v Ψ }}} remove v {{{ u, RET u; ⌜u = NONEV⌝ ∨ ∃ x, ⌜u = SOMEV x⌝ ∗ Ψ x }}}.
  Proof.
    iIntros (ϕ) "Hb Hcont".
    iDestruct "Hb" as (ℓ u γ) "[% #IL]"; subst.
    wp_lam. wp_pures.
    wp_apply (acquire_spec with "IL"); first done.
    iIntros (v) "[P HLocked]". iDestruct "P" as (b) "[Hp Hb]".
    wp_load.
    destruct b as [| | |b|b]; try (iDestruct "Hb" as "%"; contradiction).
    - wp_smart_apply (release_spec with "[$IL $HLocked Hp Hb]"); first done.
      { iExists _. iFrame. }
      iIntros. wp_pures. iApply "Hcont". iLeft. done.
    - destruct b; try (iDestruct "Hb" as "%"; contradiction).
      simpl. iDestruct "Hb" as "[Hψ Hb]".
      wp_store.
      wp_smart_apply (release_spec with "[$IL $HLocked Hp Hb]"); first done.
      { iExists _. iFrame. }
      iIntros (_).
      wp_pures.
      iApply "Hcont".
      iRight. iExists _. by iFrame.
  Qed.

End spec.
