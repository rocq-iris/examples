From stdpp Require Import namespaces.
From iris.program_logic Require Export weakestpre atomic.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import frac auth gmap csum.

Definition new_stack: val := λ: <>, ref (ref NONE).

Definition push: val :=
  rec: "push" "s" "x" :=
      let: "hd" := !"s" in
      let: "s'" := ref (SOME ("x", "hd")) in
      if: CAS "s" "hd" "s'"
        then #()
        else "push" "s" "x".

Definition pop: val :=
  rec: "pop" "s" :=
      let: "hd" := !"s" in
      match: !"hd" with
        SOME "cell" =>
        if: CAS "s" "hd" (Snd "cell")
          then SOME (Fst "cell")
          else "pop" "s"
      | NONE => NONE
      end.

Definition iter: val :=
  rec: "iter" "hd" "f" :=
      match: !"hd" with
        NONE => #()
      | SOME "cell" => "f" (Fst "cell") ;; "iter" (Snd "cell") "f"
      end.

Section proof.
  Context `{!heapGS Σ} (N: namespace).

  Fixpoint is_list (hd: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => hd ↦□ NONEV
    | x :: xs => ∃ hd': loc, hd ↦□ SOMEV (x, #hd') ∗ is_list hd' xs
    end.

  Global Instance is_list_persistent hd xs : Persistent (is_list hd xs).
  Proof. revert hd. induction xs; simpl; apply _. Qed.

  Lemma uniq_is_list xs ys hd : is_list hd xs ∗ is_list hd ys ⊢ ⌜xs = ys⌝.
  Proof.
    revert ys hd. induction xs as [|x xs' IHxs']; intros ys hd.
    - induction ys as [|y ys' IHys'].
      + auto.
      + iIntros "[Hxs Hys] /=".
        iDestruct "Hys" as (hd') "[Hhd Hys']".
        by iDestruct (pointsto_agree with "Hxs Hhd") as %?.
    - induction ys as [|y ys' IHys'].
      + iIntros "[Hxs Hys] /=".
        iDestruct "Hxs" as (?) "[Hhd _]".
        by iDestruct (pointsto_agree with "Hhd Hys") as %?.
      + iIntros "[Hxs Hys] /=".
        iDestruct "Hxs" as (?) "[Hhd Hxs']".
        iDestruct "Hys" as (?) "[Hhd' Hys']".
        iDestruct (pointsto_agree with "Hhd Hhd'") as %[= -> ->].
        by iDestruct (IHxs' with "[$Hxs' $Hys']") as %->.
  Qed.

  Definition is_stack (s: loc) xs: iProp Σ := (∃ hd: loc, s ↦ #hd ∗ is_list hd xs)%I.

  Global Instance is_list_timeless xs hd: Timeless (is_list hd xs).
  Proof. generalize hd. induction xs; apply _. Qed.

  Global Instance is_stack_timeless xs hd: Timeless (is_stack hd xs).
  Proof. generalize hd. induction xs; apply _. Qed.

  Lemma new_stack_spec:
    {{{ True }}} new_stack #() {{{ s, RET #s; is_stack s [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_bind (ref NONE)%E. wp_alloc l as "Hl".
    iMod (pointsto_persist with "Hl") as "Hl".
    wp_alloc l' as "Hl'".
    iApply "HΦ". rewrite /is_stack. auto.
  Qed.

  Lemma push_atomic_spec (s: loc) (x: val) :
    ⊢ <<{ ∀∀ (xs : list val), is_stack s xs }>>
        push #s x @ ∅
      <<{ is_stack s (x::xs) | RET #() }>>.
  Proof.
    unfold is_stack.
    iIntros (Φ) "HP". iLöb as "IH". wp_rec.
    wp_let. wp_bind (! _)%E.
    iMod "HP" as (xs) "[Hxs [Hvs' _]]".
    iDestruct "Hxs" as (hd) "[Hs Hhd]".
    wp_load. iMod ("Hvs'" with "[Hs Hhd]") as "HP"; first by eauto with iFrame.
    iModIntro. wp_let. wp_alloc l as "Hl". wp_let.
    iMod (pointsto_persist with "Hl") as "Hl".
    wp_bind (CmpXchg _ _ _)%E.
    iMod "HP" as (xs') "[Hxs' Hvs']".
    iDestruct "Hxs'" as (hd') "[Hs' Hhd']".
    destruct (decide (hd = hd')) as [->|Hneq].
    * wp_cmpxchg_suc. iDestruct "Hvs'" as "[_ Hvs']".
      iMod ("Hvs'" with "[-]") as "HQ".
      { simpl. by eauto 10 with iFrame. }
      iModIntro. wp_pures. eauto.
    * wp_cmpxchg_fail.
      iDestruct "Hvs'" as "[Hvs' _]".
      iMod ("Hvs'" with "[-]") as "HP"; first by eauto with iFrame.
      iModIntro. wp_pures. by iApply "IH".
  Qed.

  Lemma pop_atomic_spec (s: loc) :
    ⊢ <<{ ∀∀ (xs : list val), is_stack s xs }>>
        pop #s @ ∅
      <<{ match xs with [] => is_stack s []
                  | x::xs' => is_stack s xs' end
        | RET match xs with [] => NONEV | x :: _ => SOMEV x end }>>.
  Proof.
    unfold is_stack.
    iIntros (Φ) "HP". iLöb as "IH". wp_rec.
    wp_bind (! _)%E.
    iMod "HP" as (xs) "[Hxs Hvs']".
    iDestruct "Hxs" as (hd) "[Hs #Hhd]".
    destruct xs as [|y' xs'].
    - simpl. wp_load. iDestruct "Hvs'" as "[_ Hvs']".
      iMod ("Hvs'" with "[-]") as "HQ".
      { eauto with iFrame. }
      iModIntro. wp_let. wp_load. wp_pures.
      eauto.
    - simpl. iDestruct "Hhd" as (hd') "(Hhd & Hxs')".
      wp_load. iDestruct "Hvs'" as "[Hvs' _]".
      iMod ("Hvs'" with "[-]") as "HP".
      { eauto with iFrame. }
      iModIntro. wp_let. wp_load. wp_match. wp_proj.
      wp_bind (CmpXchg _ _ _).
      iMod "HP" as (xs'') "[Hxs'' Hvs']".
    iDestruct "Hxs''" as (hd'') "[Hs'' Hhd'']".
      destruct (decide (hd = hd'')) as [->|Hneq].
      + wp_cmpxchg_suc. iDestruct "Hvs'" as "[_ Hvs']".
        destruct xs'' as [|x'' xs'']; simpl.
        { by iDestruct (pointsto_agree with "Hhd Hhd''") as %?. }
        iDestruct "Hhd''" as (hd''') "[Hhd'' Hxs'']".
        iDestruct (@pointsto_agree with "Hhd Hhd''") as %[= -> ->].
        iMod ("Hvs'" with "[-]") as "HQ".
        { eauto with iFrame.  }
        iModIntro. wp_pures. eauto.
      + wp_cmpxchg_fail. iDestruct "Hvs'" as "[Hvs' _]".
        iMod ("Hvs'" with "[-]") as "HP"; first by eauto with iFrame.
        iModIntro. wp_pures. by iApply "IH".
  Qed.
End proof.
