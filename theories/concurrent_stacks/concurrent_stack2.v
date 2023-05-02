From iris.heap_lang Require Import notation proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.
From iris_examples.concurrent_stacks Require Import specs.
From iris.prelude Require Import options.

(** Stack 2: Helping, bag spec. *)

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

Definition new_stack : val := λ: "_", (mk_mailbox #(), ref NONEV).
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
Class channelG Σ := { channel_inG :: inG Σ channelR }.
Definition channelΣ : gFunctors := #[GFunctor channelR].
Global Instance subG_channelΣ {Σ} : subG channelΣ Σ → channelG Σ.
Proof. solve_inG. Qed.

Section side_channel.
  Context `{!heapGS Σ, !channelG Σ} (N : namespace).
  Implicit Types l : loc.

  Definition revoke_tok γ := own γ (Excl ()).

  Definition stages γ (P : val → iProp Σ) l v :=
    ((l ↦ #0 ∗ P v)
     ∨ (l ↦ #1)
     ∨ (l ↦ #2 ∗ revoke_tok γ))%I.

  Definition is_offer γ (P : val → iProp Σ) (v : val) : iProp Σ :=
    (∃ v' l, ⌜v = (v', #l)%V⌝ ∗ inv N (stages γ P l v'))%I.

  Lemma mk_offer_works P v :
    {{{ P v }}} mk_offer v {{{ o γ, RET o; is_offer γ P o ∗ revoke_tok γ }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (stages γ P l v) with "[Hl HP]") as "#Hinv".
    { iNext; iLeft; iFrame. }
    wp_pures; iModIntro; iApply "HΦ"; iFrame; iExists _, _; auto.
  Qed.

  (* A partial specification for revoke that will be useful later *)
  Lemma revoke_works γ P v :
    {{{ is_offer γ P v ∗ revoke_tok γ }}}
      revoke_offer v
    {{{ v', RET v'; (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ P v'') ∨ ⌜v' = InjLV #()⌝ }}}.
  Proof.
    iIntros (Φ) "[Hinv Hγ] HΦ". iDestruct "Hinv" as (v' l) "[-> #Hinv]".
    wp_lam. wp_bind (CmpXchg _ _ _). wp_pures.
    iInv N as "Hstages" "Hclose".
    iDestruct "Hstages" as "[[Hl HP] | [H | [Hl H]]]".
    - wp_cmpxchg_suc.
      iMod ("Hclose" with "[Hl Hγ]") as "_".
      { iRight; iRight; iFrame. }
      iModIntro. wp_pures. iModIntro.
      by iApply "HΦ"; iLeft; iExists _; iSplit.
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[H]") as "_".
      { iRight; iLeft; auto. }
      iModIntro.
      wp_pures.
      by iApply "HΦ"; iRight.
    - wp_cmpxchg_fail.
      iCombine "H Hγ" gives %[].
  Qed.

  (* A partial specification for take that will be useful later *)
  Lemma take_works γ P o :
    {{{ is_offer γ P o }}}
      take_offer o
    {{{ v', RET v'; (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ P v'') ∨ ⌜v' = InjLV #()⌝ }}}.
  Proof.
    iIntros (Φ) "H HΦ"; iDestruct "H" as (v l) "[-> #Hinv]".
    wp_lam. wp_proj. wp_bind (CmpXchg _ _ _).
    iInv N as "Hstages" "Hclose".
    iDestruct "Hstages" as "[[H HP] | [H | [Hl Hγ]]]".
    - wp_cmpxchg_suc.
      iMod ("Hclose" with "[H]") as "_".
      { by iRight; iLeft. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; iLeft; auto.
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[H]") as "_".
      { by iRight; iLeft. }
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
End side_channel.

Section mailbox.
  Context `{!heapGS Σ, channelG Σ} (N : namespace).
  Implicit Types l : loc.

  Definition Noffer := N .@ "offer".

  Definition mailbox_inv (P : val → iProp Σ) (l : loc) : iProp Σ :=
    (l ↦ NONEV ∨ (∃ v' γ, l ↦ SOMEV v' ∗ is_offer Noffer γ P v'))%I.

  Definition is_mailbox (P : val → iProp Σ) (v : val) : iProp Σ :=
    (∃ l, ⌜v = #l⌝ ∗ inv N (mailbox_inv P l))%I.

  Theorem mk_mailbox_works (P : val → iProp Σ) :
    {{{ True }}} mk_mailbox #() {{{ v, RET v; is_mailbox P v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_alloc l as "Hl".
    iMod (inv_alloc N _ (mailbox_inv P l) with "[Hl]") as "#Hinv".
    { by iNext; iLeft. }
    iModIntro.
    iApply "HΦ"; iExists _; eauto.
  Qed.

  Theorem get_works (P : val → iProp Σ) mailbox :
    {{{ is_mailbox P mailbox }}}
      get mailbox
    {{{ ov, RET ov; ⌜ov = NONEV⌝ ∨ ∃ v, ⌜ov = SOMEV v⌝ ∗ P v}}}.
  Proof.
    iIntros (Φ) "H HΦ". iDestruct "H" as (l) "[-> #Hinv]".
    wp_lam. wp_bind (Load _).
    iInv N as "[Hnone | Hsome]" "Hclose".
    - wp_load.
      iMod ("Hclose" with "[Hnone]") as "_".
      { by iNext; iLeft. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; auto.
    - iDestruct "Hsome" as (v' γ) "[Hl #Hoffer]".
      wp_load.
      iMod ("Hclose" with "[Hl]") as "_".
      { by iNext; iRight; iExists _, _; iFrame. }
      iModIntro.
      wp_let. wp_match.
      iApply (take_works with "Hoffer").
      iNext; iIntros (offer) "[Hsome | Hnone]".
      * iDestruct "Hsome" as (v'') "[-> HP]".
        iApply ("HΦ" with "[HP]"); iRight; auto.
      * iApply "HΦ"; iLeft; auto.
  Qed.

  Theorem put_works (P : val → iProp Σ) (mailbox v : val) :
    {{{ is_mailbox P mailbox ∗ P v }}}
      put mailbox v
    {{{ o, RET o; (∃ v', ⌜o = SOMEV v'⌝ ∗ P v') ∨ ⌜o = NONEV⌝ }}}.
  Proof.
    iIntros (Φ) "[Hmailbox HP] HΦ"; iDestruct "Hmailbox" as (l) "[-> #Hmailbox]".
    wp_lam. wp_let. wp_apply (mk_offer_works with "HP").
    iIntros (offer γ) "[#Hoffer Hrevoke]".
    wp_let. wp_bind (Store _ _). wp_pures.
    iInv N as "[HNone | HSome]" "Hclose".
    - wp_store.
      iMod ("Hclose" with "[HNone]") as "_".
      { by iNext; iRight; iExists _, _; iFrame. }
      iModIntro.
      wp_pures.
      wp_apply (revoke_works with "[Hrevoke]"); first by iFrame.
      iIntros (v') "H"; iDestruct "H" as "[HSome | HNone]".
      * iApply ("HΦ" with "[HSome]"); by iLeft.
      * iApply ("HΦ" with "[HNone]"); by iRight.
    - iDestruct "HSome" as (v' γ') "[Hl #Hoffer']".
      wp_store.
      iMod ("Hclose" with "[Hl]") as "_".
      { by iNext; iRight; iExists _, _; iFrame. }
      iModIntro.
      wp_pures.
      wp_apply (revoke_works with "[Hrevoke]"); first by iFrame.
      iIntros (v'') "H"; iDestruct "H" as "[HSome | HNone]".
      * iApply ("HΦ" with "[HSome]"); by iLeft.
      * iApply ("HΦ" with "[HNone]"); by iRight.
  Qed.
End mailbox.

Section stack_works.
  Context `{!heapGS Σ, channelG Σ} (N : namespace).
  Implicit Types l : loc.

  Definition Nmailbox := N .@ "mailbox".

  Definition oloc_to_val (ol: option loc) : val :=
    match ol with
    | None => NONEV
    | Some loc => SOMEV (#loc)
    end.
  Local Instance oloc_to_val_inj : Inj (=) (=) oloc_to_val.
  Proof. intros [|][|]; simpl; congruence. Qed.

  Definition is_list_pre (P : val → iProp Σ) (F : option loc -d> iPropO Σ) :
     option loc -d> iPropO Σ := λ v, match v with
     | None => True
     | Some l => ∃ (h : val) (t : option loc), l ↦□ (h, oloc_to_val t)%V ∗ P h ∗ ▷ F t
     end%I.

  Local Instance is_list_contr (P : val → iProp Σ) : Contractive (is_list_pre P).
  Proof. solve_contractive. Qed.

  Definition is_list_def (P : val -> iProp Σ) := fixpoint (is_list_pre P).
  Definition is_list_aux P : seal (@is_list_def P). Proof. by eexists. Qed.
  Definition is_list P := unseal (is_list_aux P).
  Definition is_list_eq P : @is_list P = @is_list_def P := seal_eq (is_list_aux P).

  Lemma is_list_unfold (P : val → iProp Σ) v :
    is_list P v ⊣⊢ is_list_pre P (is_list P) v.
  Proof.
    rewrite is_list_eq. apply (fixpoint_unfold (is_list_pre P)).
  Qed.

  Lemma is_list_dup (P : val → iProp Σ) v :
    is_list P v -∗ is_list P v ∗ match v with
      | None => True
      | Some l => ∃ h t, l ↦□ (h, oloc_to_val t)%V
      end.
  Proof.
    iIntros "Hstack". iDestruct (is_list_unfold with "Hstack") as "Hstack".
    destruct v as [l|].
    - iDestruct "Hstack" as (h t) "[#Hl Hlist]".
      rewrite (is_list_unfold _ (Some _)); iSplitL; iExists _, _; by iFrame.
    - rewrite is_list_unfold; iSplitR; eauto.
  Qed.

  Definition stack_inv P l := (∃ v, l ↦ oloc_to_val v ∗ is_list P v)%I.
  Definition is_stack P v :=
    (∃ mailbox l, ⌜v = (mailbox, #l)%V⌝ ∗ is_mailbox Nmailbox P mailbox ∗ inv N (stack_inv P l))%I.

  Theorem new_stack_spec P :
    {{{ True }}} new_stack #() {{{ v, RET v; is_stack P v }}}.
  Proof.
    iIntros (ϕ) "_ Hpost".
    wp_lam.
    wp_alloc l as "Hl".
    wp_apply mk_mailbox_works; first done.
    iIntros (mailbox) "#Hmailbox".
    iMod (inv_alloc N _ (stack_inv P l) with "[Hl]") as "#Hinv".
    { iNext; iExists None; iFrame. rewrite is_list_unfold. done. }
    wp_pures; iModIntro; iApply "Hpost"; iExists _, _; auto.
  Qed.

  Theorem push_spec P s v :
    {{{ is_stack P s ∗ P v }}} push s v {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[Hstack HP] HΦ". iDestruct "Hstack" as (mailbox l) "(-> & #Hmailbox & #Hinv)".
    iLöb as "IH" forall (v).
    wp_lam. wp_let. wp_proj. wp_let. wp_proj. wp_let.
    wp_apply (put_works _ P with "[HP]"); first by iFrame.
    iIntros (result) "Hopt".
    iDestruct "Hopt" as "[HSome | ->]".
    - iDestruct "HSome" as (v') "[-> HP]".
      wp_match. wp_bind (Load _).
      iInv N as (v'') "[Hl Hlist]" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Hl Hlist]") as "_".
      { iNext; iExists _; iFrame. }
      iModIntro.
      wp_let. wp_alloc l' as "Hl'". wp_pures. wp_bind (CmpXchg _ _ _).
      iInv N as (list) "(Hl & Hlist)" "Hclose".
      destruct (decide (v'' = list)) as [ -> |].
      * wp_cmpxchg_suc. { destruct list; left; done. }
        iMod (mapsto_persist with "Hl'") as "#Hl'".
        iMod ("Hclose" with "[HP Hl Hlist]") as "_".
        { iNext; iExists (Some _); iFrame.
          rewrite (is_list_unfold _ (Some _)). iExists _, _; iFrame; eauto. }
        iModIntro.
        wp_pures.
        by iApply "HΦ".
      * wp_cmpxchg_fail.
        { destruct list, v''; simpl; congruence. }
        { destruct list; left; done. }
        iMod ("Hclose" with "[Hl Hlist]") as "_".
        { iNext; iExists _; by iFrame. }
        iModIntro.
        wp_pures.
        iApply ("IH" with "HP HΦ").
    - wp_match.
      by iApply "HΦ".
  Qed.

  Theorem pop_spec P s :
    {{{ is_stack P s }}} pop s {{{ ov, RET ov; ⌜ov = NONEV⌝ ∨ ∃ v, ⌜ov = SOMEV v⌝ ∗ P v }}}.
  Proof.
    iIntros (Φ) "Hstack HΦ". iDestruct "Hstack" as (mailbox l) "(-> & #Hmailbox & #Hstack)".
    iLöb as "IH".
    wp_lam. wp_proj. wp_let. wp_proj. wp_pures.
    wp_apply get_works; first done.
    iIntros (ov) "[-> | HSome]".
    - wp_match. wp_bind (Load _).
      iInv N as (list) "[Hl Hlist]" "Hclose".
      wp_load.
      iDestruct (is_list_dup with "Hlist") as "[Hlist Hlist2]".
      iMod ("Hclose" with "[Hl Hlist]") as "_".
      { iNext; iExists _; by iFrame. }
      iModIntro.
      destruct list as [list|]; last first.
      * wp_match.
        iApply "HΦ"; by iLeft.
      * wp_match. wp_bind (Load _).
        iInv N as (v') "[>Hl Hlist]" "Hclose".
        iDestruct "Hlist2" as (??) "Hl'".
        wp_load.
        iMod ("Hclose" with "[Hl Hlist]") as "_".
        { iNext; iExists _; by iFrame. }
        iModIntro.
        wp_let. wp_proj. wp_bind (CmpXchg _ _ _). wp_pures.
        iInv N as (v'') "[Hl Hlist]" "Hclose".
        destruct (decide (v'' = Some list)) as [-> |].
        + rewrite is_list_unfold.
          iDestruct "Hlist" as (h' t') "(Hl'' & HP & Hlist)".
          wp_cmpxchg_suc.
          iDestruct (mapsto_agree with "Hl'' Hl'") as "%"; simplify_eq.
          iMod ("Hclose" with "[Hl Hlist]") as "_".
          { iNext; iExists _; by iFrame. }
          iModIntro.
          wp_pures.
          iApply ("HΦ" with "[HP]"); iRight; iExists _; by iFrame.
        + wp_cmpxchg_fail. { destruct v''; simpl; congruence. }
          iMod ("Hclose" with "[Hl Hlist]") as "_".
          { iNext; iExists _; by iFrame. }
          iModIntro.
          wp_pures.
          iApply ("IH" with "HΦ").
    - iDestruct "HSome" as (v) "[-> HP]".
      wp_pures.
      iApply "HΦ"; iRight; iExists _; auto.
  Qed.
End stack_works.

Program Definition spec {Σ} N `{heapGS Σ, channelG Σ} : concurrent_bag Σ :=
  {| is_bag := is_stack N; new_bag := new_stack; bag_push := push; bag_pop := pop |} .
Solve Obligations of spec with eauto using pop_spec, push_spec, new_stack_spec.
