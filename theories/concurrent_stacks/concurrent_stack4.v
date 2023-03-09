From iris.base_logic Require Import invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import excl.
From iris_examples.concurrent_stacks Require Import specs.
From iris.prelude Require Import options.

(** Stack 4: Helping, CAP spec. *)

Definition mk_offer : val :=
  λ: "v", ("v", ref #0).
Definition revoke_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #2 then SOME (Fst "v") else NONE.
Definition take_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #1 then SOME (Fst "v") else NONE.

Definition mk_mailbox : val := λ: "_", ref NONEV.
Definition put : val :=
  λ: "r" "v",
    let: "off" := mk_offer "v" in
    "r" <- SOME "off";;
    revoke_offer "off".
Definition get : val :=
  λ: "r",
    let: "offopt" := !"r" in
    match: "offopt" with
      NONE => NONE
    | SOME "x" => take_offer "x"
    end.

Definition mk_stack : val := λ: "_", (mk_mailbox #(), ref NONEV).
Definition push : val :=
  rec: "push" "p" "v" :=
    let: "mailbox" := Fst "p" in
    let: "s" := Snd "p" in
    match: put "mailbox" "v" with
      NONE => #()
    | SOME "v'" =>
      let: "tail" := ! "s" in
      let: "new" := SOME (ref ("v'", "tail")) in
      if: CAS "s" "tail" "new" then #() else "push" "p" "v'"
    end.
Definition pop : val :=
  rec: "pop" "p" :=
    let: "mailbox" := Fst "p" in
    let: "s" := Snd "p" in
    match: get "mailbox" with
      NONE =>
      match: !"s" with
        NONE => NONEV
      | SOME "l" =>
        let: "pair" := !"l" in
        if: CAS "s" (SOME "l") (Snd "pair")
        then SOME (Fst "pair")
        else "pop" "p"
      end
    | SOME "x" => SOME "x"
    end.

Definition channelR := exclR unitR.
Class channelG Σ := {channel_inG :> inG Σ channelR}.

Section proofs.
  Context `{!heapGS Σ, !channelG Σ} (N : namespace).

  Implicit Types l : loc.

  Definition Nside_channel := N .@ "side_channel".
  Definition Nstack := N .@ "stack".
  Definition Nmailbox := N .@ "mailbox".

  Definition inner_mask : coPset := ⊤ ∖ ↑Nside_channel ∖ ↑Nstack.

  Lemma inner_mask_includes :
     ⊤ ∖ ↑ N ⊆ inner_mask.
  Proof. solve_ndisj. Qed.

  Lemma inner_mask_promote (P Q : iProp Σ) :
     (P ={⊤ ∖ ↑ N}=∗ Q) -∗ (P ={inner_mask}=∗ Q).
  Proof.
    iIntros "Himp P".
    iMod (fupd_mask_subseteq (⊤ ∖ ↑ N)) as "H"; first by apply inner_mask_includes.
    iDestruct ("Himp" with "P") as "HQ".
    iMod "HQ".
    by iMod "H".
  Qed.

  Definition revoke_tok γ := own γ (Excl ()).
  Definition can_push P Q v : iProp Σ :=
    (∀ (xs : list val), P xs ={inner_mask}=∗ P (v :: xs) ∗ Q #())%I.
  Definition access_inv (P : list val → iProp Σ) : iProp Σ :=
    (|={⊤ ∖ ↑Nside_channel, inner_mask}=> ∃ vs, (▷ P vs) ∗
      ((▷ P vs) ={inner_mask, ⊤ ∖ ↑Nside_channel}=∗ True))%I.

  Definition stages γ P Q l (v : val) :=
    ((l ↦ #0 ∗ can_push P Q v)  ∨
     (l ↦ #1 ∗ Q #()) ∨
     (l ↦ #1 ∗ revoke_tok γ) ∨
     (l ↦ #2 ∗ revoke_tok γ))%I.

  Definition is_offer γ P Q (v : val) : iProp Σ :=
    (∃ v' l, ⌜v = (v', #l)%V⌝ ∗ inv Nside_channel (stages γ P Q l v'))%I.

  Lemma mk_offer_works P Q v :
    {{{ can_push P Q v }}}
      mk_offer v
    {{{ o γ, RET o; is_offer γ P Q o ∗ revoke_tok γ }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc Nside_channel _ (stages γ P Q l v) with "[Hl HP]") as "#Hinv".
    { iNext; iLeft; iFrame. }
    wp_pures; iModIntro; iApply "HΦ"; iFrame; iExists _, _; auto.
  Qed.

  Lemma revoke_works γ P Q v :
    {{{ is_offer γ P Q v ∗ revoke_tok γ }}}
      revoke_offer v
    {{{ v', RET v'; (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ can_push P Q v'') ∨ (⌜v' = InjLV #()⌝ ∗ (Q #())) }}}.
  Proof.
    iIntros (Φ) "[Hinv Hγ] HΦ". iDestruct "Hinv" as (v' l) "[-> #Hinv]".
    wp_lam. wp_pures. wp_bind (CmpXchg _ _ _).
    iInv Nside_channel as "Hstages" "Hclose".
    iDestruct "Hstages" as "[[Hl HP] | [[Hl HQ] | [[Hl H] | [Hl H]]]]".
    - wp_cmpxchg_suc.
      iMod ("Hclose" with "[Hl Hγ]") as "_".
      { iNext; iRight; iRight; iFrame. }
      iModIntro.
      wp_pures.
      by iApply "HΦ"; iLeft; iExists _; iFrame.
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[Hl Hγ]") as "_".
      { iNext; iRight; iRight; iLeft; iFrame. }
      iModIntro.
      wp_pures.
      iApply ("HΦ" with "[HQ]"); iRight; auto.
    - wp_cmpxchg_fail.
      iCombine "H Hγ" gives %[].
    - wp_cmpxchg_fail.
      iCombine "H Hγ" gives %[].
  Qed.

  Lemma take_works γ P Q Q' o Ψ :
    let do_pop : iProp Σ :=
        (∀ v xs, P (v :: xs) ={inner_mask}=∗ P xs ∗ Ψ (SOMEV v))%I in
    {{{ is_offer γ P Q o ∗ access_inv P ∗ (do_pop ∧ Q') }}}
      take_offer o
    {{{ v', RET v';
        (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ Ψ v') ∨ (⌜v' = InjLV #()⌝ ∗ (do_pop ∧ Q')) }}}.
  Proof.
    simpl; iIntros (Φ) "[H [Hopener Hupd]] HΦ"; iDestruct "H" as (v l) "[-> #Hinv]".
    wp_lam. wp_proj. wp_bind (CmpXchg _ _ _).
    iInv Nside_channel as "Hstages" "Hclose".
    iDestruct "Hstages" as "[[Hl Hpush] | [[Hl HQ] | [[Hl Hγ] | [Hl Hγ]]]]".
    - iMod "Hopener" as (xs) "[HP Hcloser]".
      wp_cmpxchg_suc.
      iMod ("Hpush" with "HP") as "[HP HQ]".
      iMod ("Hupd" with "HP") as "[HP HΨ]".
      iMod ("Hcloser" with "HP") as "_".
      iMod ("Hclose" with "[Hl HQ]") as "_".
      { iRight; iLeft; iFrame. }
      iApply fupd_mask_intro_subseteq; first done.
      wp_pures.
      iApply "HΦ"; iLeft; auto.
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[Hl HQ]") as "_".
      { iRight; iLeft; iFrame. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; auto.
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[Hl Hγ]").
      { iRight; iRight; iFrame. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; auto.
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[Hl Hγ]").
      { iRight; iRight; iFrame. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; auto.
  Qed.

  Definition mailbox_inv P l : iProp Σ :=
    (l ↦ NONEV ∨ (∃ v' γ Q, l ↦ SOMEV v' ∗ is_offer γ P Q v'))%I.

  Definition is_mailbox P v : iProp Σ :=
    (∃ l, ⌜v = #l⌝ ∗ inv Nmailbox (mailbox_inv P l))%I.

  Lemma mk_mailbox_works P :
    {{{ True }}} mk_mailbox #() {{{ v, RET v; is_mailbox P v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc l as "Hl".
    iMod (inv_alloc Nmailbox _ (mailbox_inv P l) with "[Hl]") as "#Hinv".
    { iNext; by iLeft. }
    iModIntro.
    iApply "HΦ"; iExists _; auto.
  Qed.

  Lemma get_works Q P Ψ mailbox :
    let do_pop : iProp Σ :=
        (∀ v xs, P (v :: xs) ={inner_mask}=∗ P xs ∗ Ψ (SOMEV v))%I in
    {{{ is_mailbox P mailbox ∗ access_inv P ∗ (do_pop ∧ Q) }}}
      get mailbox
    {{{ ov, RET ov; (∃ v, ⌜ov = SOMEV v⌝ ∗ Ψ ov) ∨ (⌜ov = NONEV⌝ ∗ (do_pop ∧ Q)) }}}.
  Proof.
    simpl; iIntros (Φ) "[Hmail [Hopener Hpush]] HΦ". iDestruct "Hmail" as (l) "[-> #Hmail]".
    wp_lam. wp_bind (Load _).
    iInv Nmailbox as "[Hnone | Hsome]" "Hclose".
    - wp_load.
      iMod ("Hclose" with "[Hnone]") as "_".
      { by iLeft. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; iRight; by iFrame.
    - iDestruct "Hsome" as (v' γ Q') "[Hl #Hoffer]".
      wp_load.
      iMod ("Hclose" with "[Hl Hoffer]") as "_".
      { iNext; iRight; iExists _, _, _; by iFrame. }
      iModIntro.
      wp_let. wp_match. wp_apply (take_works with "[Hpush Hopener]"); by iFrame.
  Qed.

  Lemma put_works P Q mailbox v :
    {{{ is_mailbox P mailbox ∗ can_push P Q v }}}
      put mailbox v
    {{{ o, RET o; (∃ v', ⌜o = SOMEV v'⌝ ∗ can_push P Q v') ∨ (⌜o = NONEV⌝ ∗ Q #()) }}}.
  Proof.
    iIntros (Φ) "[Hmail Hpush] HΦ". iDestruct "Hmail" as (l) "[-> #Hmail]".
    wp_lam. wp_let. wp_apply (mk_offer_works with "Hpush").
    iIntros (o γ) "[#Hoffer Hrev]".
    wp_let. wp_bind (Store _ _). wp_pures.
    iInv Nmailbox as "[Hnone | Hsome]" "Hclose".
    - wp_store.
      iMod ("Hclose" with "[Hnone]") as "_".
      { iNext; iRight; iExists _, _, _; by iFrame. }
      iModIntro.
      wp_pures.
      wp_apply (revoke_works with "[Hrev]"); first auto.
      iIntros (v') "H"; iApply "HΦ"; auto.
    - iDestruct "Hsome" as (v' γ' Q') "[Hl _]". wp_store.
      iMod ("Hclose" with "[Hl]") as "_".
      { iNext; iRight; iExists _, _, _; by iFrame. }
      iModIntro.
      wp_pures.
      wp_apply (revoke_works with "[Hrev]"); first auto.
      iIntros (v'') "H"; iApply "HΦ"; auto.
  Qed.

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
    l ↦□ (h, t) -∗
    is_list xs (Some l) -∗
    ∃ ys, ⌜xs = h :: ys⌝.
  Proof.
    destruct xs; first by iIntros "? %".
    iIntros "Hl Hstack"; iDestruct "Hstack" as (t') "(Hl' & Hrest)".
    iDestruct (mapsto_agree with "Hl Hl'") as "%"; simplify_eq; iExists _; auto.
  Qed.

  Definition stack_inv P l :=
    (∃ v xs, l ↦ oloc_to_val v ∗ is_list xs v ∗ P xs)%I.

  Definition is_stack_pred P v :=
    (∃ mailbox l, ⌜v = (mailbox, #l)%V⌝ ∗ is_mailbox P mailbox ∗ inv Nstack (stack_inv P l))%I.

  Theorem mk_stack_works (P : list val → iProp Σ) :
    {{{ P [] }}} mk_stack #() {{{ v, RET v; is_stack_pred P v }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    wp_lam.
    wp_alloc l as "Hl".
    wp_apply mk_mailbox_works ; first done. iIntros (v) "#Hmailbox".
    iMod (inv_alloc Nstack _ (stack_inv P l) with "[Hl HP]") as "#Hinv".
    { by iNext; iExists None, []; iFrame. }
    wp_pures. iModIntro; iApply "HΦ"; iExists _; auto.
  Qed.

  Theorem push_works P s v Ψ :
    {{{ is_stack_pred P s ∗ ∀ xs, P xs ={⊤ ∖ ↑ N}=∗ P (v :: xs) ∗ Ψ #()}}}
      push s v
    {{{ RET #(); Ψ #() }}}.
  Proof.
    iIntros (Φ) "[Hstack Hupd] HΦ". iDestruct "Hstack" as (mailbox l) "(-> & #Hmailbox & #Hinv)".
    iAssert (∀ (xs : list val), P xs ={inner_mask}=∗ P (v :: xs) ∗ Ψ #())%I with "[Hupd]" as "Hupd".
    { iIntros (xs). by iApply inner_mask_promote. }
    iLöb as "IH" forall (v).
    wp_lam. wp_pures.
    wp_apply (put_works with "[Hupd]"); first auto. iIntros (o) "H".
    iDestruct "H" as "[Hsome | [-> HΨ]]".
    - iDestruct "Hsome" as (v') "[-> Hupd]".
      wp_match.
      wp_bind (Load _).
      iInv Nstack as (list xs) "(Hl & Hlist & HP)" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Hl Hlist HP]") as "_".
      { iNext; iExists _, _; iFrame. }
      clear xs.
      iModIntro.
      wp_let. wp_alloc l' as "Hl'". wp_pures. wp_bind (CmpXchg _ _ _).
      iInv Nstack as (list' xs) "(Hl & Hlist & HP)" "Hclose".
      destruct (decide (list = list')) as [ -> |].
      * wp_cmpxchg_suc. { destruct list'; left; done. }
        iMod (mapsto_persist with "Hl'") as "#Hl'".
        iMod (fupd_mask_subseteq inner_mask) as "Hupd'"; first solve_ndisj.
        iMod ("Hupd" with "HP") as "[HP HΨ]".
        iMod "Hupd'" as "_".
        iMod ("Hclose" with "[Hl HP Hlist]") as "_".
        { iNext; iExists (Some _), (v' :: xs); iFrame; iExists _; iFrame; auto. }
        iModIntro.
        wp_pures.
        by iApply ("HΦ" with "HΨ").
      * wp_cmpxchg_fail.
      { destruct list, list'; simpl; congruence. }
      { destruct list'; left; done. }
        iMod ("Hclose" with "[Hl HP Hlist]").
        { iExists _, _; iFrame. }
        iModIntro.
        wp_pures.
        iApply ("IH" with "HΦ Hupd").
    - wp_match. iApply ("HΦ" with "HΨ").
  Qed.

  Theorem pop_works P s Ψ :
    {{{ is_stack_pred P s ∗
        (∀ v xs, P (v :: xs) ={⊤ ∖ ↑ N}=∗ P xs ∗ Ψ (SOMEV v)) ∧
        (P [] ={⊤ ∖ ↑ N}=∗ P [] ∗ Ψ NONEV) }}}
      pop s
    {{{ v, RET v; Ψ v }}}.
  Proof.
    iIntros (Φ) "(Hstack & Hupd) HΦ".
    iDestruct "Hstack" as (mailbox l) "(-> & #Hmailbox & #Hinv)".
    iDestruct (bi.and_mono_r with "Hupd") as "Hupd"; first apply inner_mask_promote.
    iDestruct (bi.and_mono_l _ _ (∀ (v : val) (xs : list val), _)%I with "Hupd") as "Hupd".
    { iIntros "Hupdcons". iIntros (v xs). iSpecialize ("Hupdcons" $! v xs). iApply (inner_mask_promote with "Hupdcons"). }
    iLöb as "IH".
    wp_lam. wp_proj. wp_let. wp_proj. wp_let.
    wp_apply (get_works _ _ (λ v, Ψ v) with "[Hupd]").
    { iSplitR; first done.
      iFrame.
      iInv Nstack as (v xs) "(Hl & Hlist & HP)" "Hclose".
      iModIntro.
      iExists xs; iSplitL "HP"; first auto.
      iIntros "HP".
      iMod ("Hclose" with "[HP Hl Hlist]") as "_".
      { iNext; iExists _, _; iFrame. }
      auto. }
    iIntros (ov) "[Hsome | [-> Hupd]]".
    - iDestruct "Hsome" as (v) "[-> HΨ]".
      wp_pures.
      iApply ("HΦ" with "HΨ").
    - wp_match. wp_bind (Load _).
      iInv Nstack as (v xs) "(Hl & Hlist & HP)" "Hclose".
      wp_load.
      iDestruct (is_list_dup with "Hlist") as "[Hlist H]".
    destruct v as [l'|]; last first.
      * iDestruct (is_list_empty with "Hlist") as %->.
        iMod (fupd_mask_subseteq inner_mask) as "Hupd'"; first solve_ndisj.
        iMod ("Hupd" with "HP") as "[HP HΨ]".
        iMod "Hupd'" as "_".
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_match.
        iApply ("HΦ" with "HΨ").
      * iDestruct "H" as (h t) "Hl'".
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_match. wp_bind (Load _).
        iInv Nstack as (v xs') "(Hl & Hlist & HP)" "Hclose".
        wp_load.
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_pures. wp_bind (CmpXchg _ _ _).
        iInv Nstack as (v' xs'') "(Hl & Hlist & HP)" "Hclose".
        destruct (decide (v' = (Some l'))) as [ -> |].
        + wp_cmpxchg_suc.
          iDestruct (is_list_cons with "Hl' Hlist") as (ys) "%".
          simplify_eq.
          iMod (fupd_mask_subseteq inner_mask) as "Hupd'"; first solve_ndisj.
          iDestruct "Hupd" as "[Hupdcons _]".
          iMod ("Hupdcons" with "HP") as "[HP HΨ]".
          iMod "Hupd'" as "_".
          iDestruct "Hlist" as (t') "(Hl'' & Hlist)".
          iDestruct (mapsto_agree with "Hl' Hl''") as "%"; simplify_eq.
          iMod ("Hclose" with "[Hlist Hl HP]") as "_".
          { iNext; iExists _, _; iFrame. }
          iModIntro.
          wp_pures.
          iApply ("HΦ" with "HΨ").
        + wp_cmpxchg_fail. { destruct v'; simpl; congruence. }
          iMod ("Hclose" with "[Hlist Hl HP]") as "_".
          { iNext; iExists _, _; iFrame. }
          iModIntro.
          wp_pures.
          iApply ("IH" with "HΦ Hupd").
  Qed.
End proofs.

Program Definition spec {Σ} `{heapGS Σ, channelG Σ} : concurrent_stack Σ :=
  {| is_stack := is_stack_pred; new_stack := mk_stack; stack_push := push; stack_pop := pop |} .
Solve Obligations of spec with eauto using pop_works, push_works, mk_stack_works.
