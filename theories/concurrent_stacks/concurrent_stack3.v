From iris.base_logic Require Import invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris_examples.concurrent_stacks Require Import specs.

(** Stack 3: No helping, CAP spec. *)

Definition mk_stack : val := λ: "_", ref NONEV.
Definition push : val :=
  rec: "push" "s" "v" :=
    let: "tail" := ! "s" in
    let: "new" := SOME (ref ("v", "tail")) in
    if: CAS "s" "tail" "new" then #() else "push" "s" "v".
Definition pop : val :=
  rec: "pop" "s" :=
    match: !"s" with
      NONE => NONEV
    | SOME "l" =>
      let: "pair" := !"l" in
      if: CAS "s" (SOME "l") (Snd "pair")
      then SOME (Fst "pair")
      else "pop" "s"
    end.

Section stack_works.
  Context `{!heapGS Σ} (N : namespace).
  Implicit Types l : loc.

  Definition oloc_to_val (ol: option loc) : val :=
    match ol with
    | None => NONEV
    | Some loc => SOMEV (#loc)
    end.
  Local Instance oloc_to_val_inj : Inj (=) (=) oloc_to_val.
  Proof. intros [|][|]; simpl; congruence. Qed.

  Fixpoint is_list xs v : iProp Σ :=
    (match xs, v with
     | [], None => True
     | x :: xs, Some l => ∃ t, l ↦□ (x, oloc_to_val t)%V ∗ is_list xs t
     | _, _ => False
     end)%I.

  Lemma is_list_dup xs v :
    is_list xs v -∗ is_list xs v ∗ match v with
      | None => True
      | Some l => ∃ h t, l ↦□ (h, oloc_to_val t)%V
      end.
  Proof.
    destruct xs, v; simpl; auto; first by iIntros "[]".
    iIntros "H"; iDestruct "H" as (t) "[#Hl Hstack]".
    iSplitL; first by (iExists _; iFrame). by iExists _, _.
  Qed.

  Lemma is_list_empty xs :
    is_list xs None -∗ ⌜xs = []⌝.
  Proof.
    destruct xs; iIntros "Hstack"; auto.
  Qed.

  Lemma is_list_cons xs l h t :
    l ↦□ (h, t)%V -∗
    is_list xs (Some l) -∗
    ∃ ys, ⌜xs = h :: ys⌝.
  Proof.
    destruct xs; first by iIntros "? %".
    iIntros "Hl Hstack"; iDestruct "Hstack" as (t') "(Hl' & Hrest)".
    iDestruct (pointsto_agree with "Hl Hl'") as "%"; simplify_eq; iExists _; auto.
  Qed.

  Definition stack_inv P l :=
    (∃ v xs, l ↦ oloc_to_val v ∗ is_list xs v ∗ P xs)%I.

  Definition is_stack_pred P v :=
    (∃ l, ⌜v = #l⌝ ∗ inv N (stack_inv P l))%I.

  Theorem mk_stack_spec P :
    {{{ P [] }}} mk_stack #() {{{ v, RET v; is_stack_pred P v }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    wp_lam. wp_alloc l as "Hl".
    iMod (inv_alloc N _ (stack_inv P l) with "[Hl HP]") as "#Hinv".
    { iNext; iExists None, []; iFrame. }
    iModIntro; iApply "HΦ"; iExists _; auto.
  Qed.

  Theorem push_spec P s v Ψ :
    {{{ is_stack_pred P s ∗ ∀ xs, P xs ={⊤ ∖ ↑ N}=∗ P (v :: xs) ∗ Ψ #()}}}
      push s v
    {{{ RET #(); Ψ #() }}}.
  Proof.
    iIntros (Φ) "[Hstack Hupd] HΦ". iDestruct "Hstack" as (l) "[-> #Hinv]".
    iLöb as "IH".
    wp_lam. wp_pures. wp_bind (Load _).
    iInv N as (list xs) "(Hl & Hlist & HP)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hl Hlist HP]") as "_".
    { iNext; iExists _, _; iFrame. }
    clear xs.
    iModIntro.
    wp_let. wp_alloc l' as "Hl'". wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (list' xs) "(Hl & Hlist & HP)" "Hclose".
    destruct (decide (list = list')) as [ -> |].
    - wp_cmpxchg_suc. { destruct list'; left; done. }
      iMod (pointsto_persist with "Hl'") as "#Hl'".
      iMod ("Hupd" with "HP") as "[HP HΨ]".
      iMod ("Hclose" with "[Hl HP Hlist]") as "_".
      { iNext; iExists (Some _), (v :: xs); iFrame "#∗". }
      iModIntro.
      wp_pures.
      by iApply ("HΦ" with "HΨ").
    - wp_cmpxchg_fail.
      { destruct list, list'; simpl; congruence. }
      { destruct list'; left; done. }
      iMod ("Hclose" with "[Hl HP Hlist]").
      { iExists _, _; iFrame. }
      iModIntro.
      wp_pures.
      iApply ("IH" with "Hupd HΦ").
  Qed.

  Theorem pop_spec P s Ψ :
    {{{ is_stack_pred P s ∗
        (∀ v xs, P (v :: xs) ={⊤ ∖ ↑ N}=∗ P xs ∗ Ψ (SOMEV v)) ∧
        (P [] ={⊤ ∖ ↑ N}=∗ P [] ∗ Ψ NONEV) }}}
      pop s
    {{{ v, RET v; Ψ v }}}.
  Proof.
    iIntros (Φ) "(Hstack & Hupd) HΦ".
    iDestruct "Hstack" as (l) "[-> #Hinv]".
    iLöb as "IH".
    wp_lam. wp_bind (Load _).
    iInv N as (v xs) "(Hl & Hlist & HP)" "Hclose".
    wp_load.
    iDestruct (is_list_dup with "Hlist") as "[Hlist H]".
    destruct v as [l'|]; last first.
    - iDestruct (is_list_empty with "Hlist") as %->.
      iDestruct "Hupd" as "[_ Hupdnil]".
      iMod ("Hupdnil" with "HP") as "[HP HΨ]".
      iMod ("Hclose" with "[Hlist Hl HP]") as "_".
      { iNext; iExists _, _; iFrame. }
      iModIntro.
      wp_match.
      iApply ("HΦ" with "HΨ").
    - iDestruct "H" as (h t) "Hl'".
      iMod ("Hclose" with "[Hlist Hl HP]") as "_".
      { iNext; iExists _, _; iFrame. }
      iModIntro.
      wp_match. wp_bind (Load _).
      iInv N as (v xs') "(Hl & Hlist & HP)" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Hlist Hl HP]") as "_".
      { iNext; iExists _, _; iFrame. }
      iModIntro.
      wp_let. wp_proj. wp_bind (CmpXchg _ _ _). wp_pures.
      iInv N as (v' xs'') "(Hl & Hlist & HP)" "Hclose".
      destruct (decide (v' = (Some l'))) as [ -> |].
      * wp_cmpxchg_suc.
        iDestruct (is_list_cons with "Hl' Hlist") as (ys) "%".
        simplify_eq.
        iDestruct "Hupd" as "[Hupdcons _]".
        iMod ("Hupdcons" with "HP") as "[HP HΨ]".
        iDestruct "Hlist" as (t') "(Hl'' & Hlist)".
        iDestruct (pointsto_agree with "Hl' Hl''") as "%"; simplify_eq.
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_pures.
        iApply ("HΦ" with "HΨ").
      * wp_cmpxchg_fail. { destruct v'; simpl; congruence. }
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_pures.
        iApply ("IH" with "Hupd HΦ").
  Qed.
End stack_works.

Program Definition spec {Σ} `{heapGS Σ} : concurrent_stack Σ :=
  {| is_stack := is_stack_pred; new_stack := mk_stack; stack_push := push; stack_pop := pop |} .
Solve Obligations of spec with eauto using pop_spec, push_spec, mk_stack_spec.
