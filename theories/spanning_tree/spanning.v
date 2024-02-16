From iris.algebra Require Import frac gmap gset excl.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
From iris.base_logic Require Import cancelable_invariants.
From iris.prelude Require Import options.

From iris_examples.spanning_tree Require Import graph mon.

Definition try_mark : val :=
  λ: "y", let: "e" := Fst (!"y") in CAS "e" #false #true.

Definition unmark_fst : val :=
  λ: "y",
  let: "e" := ! "y" in "y" <- (Fst "e", (NONE, Snd (Snd "e"))).

Definition unmark_snd : val :=
  λ: "y",
  let: "e" := ! "y" in "y" <- (Fst "e", (Fst (Snd "e"), NONE)).

Definition span : val :=
  rec: "span" "x" :=
  match: "x" with
    NONE => # false
  | SOME "y" =>
    if: try_mark "y" then
      let: "e" := ! "y" in
      let: "rs" := "span" (Fst (Snd "e")) ||| "span" (Snd (Snd "e")) in
      ((if: ~ (Fst "rs") then unmark_fst "y" else #())
         ;; if: ~ (Snd "rs") then unmark_snd "y" else #());; #true
    else
      #false
  end.

Section Helpers.
  Context `{heapGS Σ, cinvG Σ, graphG Σ, spawnG Σ} (κ : gname).

  Lemma wp_try_mark g Mrk k q (x : loc) : x ∈ dom g →
    graph_ctx κ g Mrk ∗ own_graph q ∅ ∗ cinv_own κ k
    ⊢ WP (try_mark #x) {{ v,
         (⌜v = #true⌝ ∗ (∃ u, ⌜(g !! x) = Some u⌝ ∗ own_graph q (x [↦] u))
          ∗ is_marked x ∗ cinv_own κ k)
           ∨ (⌜v = #false⌝ ∗ own_graph q ∅ ∗ is_marked x ∗ cinv_own κ k)
      }}.
  Proof.
    iIntros (Hgx) "(#Hgr & Hx & key)".
    wp_lam; wp_bind (! _)%E. unfold graph_ctx.
    iMod (cinv_acc with "Hgr key") as "(>Hinv & key & Hcl)"; first done.
    unfold graph_inv at 2.
    iDestruct "Hinv" as (G) "(Hi1 & Hi2 & Hi3 & Hi4)".
    iDestruct (graph_open with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    iDestruct "Hil" as (u) "[Hil1 Hil2]".
    iDestruct "Hil2" as (m) "[Hil2 [Hil3 Hil4]]".
    wp_load.
    iDestruct "Hil1" as %Hil1. iDestruct "Hil2" as %Hil2.
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3"; eauto.
    { by iFrame. }
    iMod ("Hcl" with "[Hi1 Hi2 Hi3 Hi4]") as "_".
    { iNext. unfold graph_inv at 2. iExists _; iFrame; auto. }
    iModIntro. wp_proj. wp_let.
    destruct u as [u1 u2]; simpl.
    wp_bind (CmpXchg _ _ _).
    iMod (cinv_acc _ graphN with "Hgr key")
      as "(>Hinv & key & Hclose)"; first done.
    unfold graph_inv at 2.
    iDestruct "Hinv" as (G') "(Hi1 & Hi2 & Hi3 & Hi4)".
    iDestruct (graph_open with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    iDestruct "Hil" as (u) "[Hil1 Hil2]".
    iDestruct "Hil2" as (m') "[Hil2 [Hil3 Hil4]]".
    iDestruct "Hil2" as %Hil2'. iDestruct "Hil1" as %Hil1'.
    iDestruct "Hi4" as %Hi4.
    rewrite Hil2' in Hil2; inversion Hil2; subst.
    iDestruct (auth_own_graph_valid with "Hi1") as %Hvl.
    destruct u as [[] uch].
    - wp_cmpxchg_fail.
      iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3";
      eauto.
      { by iFrame. }
      iMod (already_marked with "Hi2") as "[Hi2 Hxm]"; [|iFrame "Hxm"].
      { by eapply in_dom_of_graph. }
      iMod ("Hclose" with "[Hi1 Hi2 Hi3]") as "_".
      { iNext. unfold graph_inv at 2. iExists _; iFrame; auto. }
      iModIntro. iFrame. wp_pures. iRight; by iFrame.
    - (* CAS succeeds *)
      wp_cmpxchg_suc.
      iMod (mark_graph _ _ x uch with "[Hi1 Hx]") as "[Hi1 Hx]"; try by iFrame.
      { apply (proj1 (not_elem_of_dom (D := gset loc) G' x)).
        intros Hid. eapply in_dom_of_graph in Hid; eauto; tauto. }
      iMod (new_marked with "Hi2") as "[Hi2 Hm]". iFrame "key Hm".
      erewrite delete_marked.
      iDestruct (auth_own_graph_valid with "Hi1") as %Hvl'.
      iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3".
      { iFrame "Hi3". iExists (_, _). iFrame.
          rewrite mark_update_lookup; eauto. }
      iMod ("Hclose" with "[Hi1 Hi2 Hi3]") as "_".
      + iNext; unfold graph_inv at 2. iExists _; iFrame.
        rewrite dom_op dom_singleton_L ?gset_op (comm union); iFrame.
        iPureIntro.
        { by apply mark_strict_subgraph. }
      + iModIntro. wp_pures. iModIntro. iLeft; iSplit; trivial. iExists _; iFrame.
        iPureIntro; eapply of_graph_unmarked; eauto.
  Qed.

  Lemma laod_strict_sub_children g G x w u : g !! x = Some u →
    strict_subgraph g (Gmon_graph ((x [↦] w) ⋅ delete x G)) →
    strict_sub_children u w.
  Proof.
    move => Hgx /(_ x).
    rewrite /get_left /get_right /Gmon_graph Hgx ?lookup_omap ?lookup_op
      ?lookup_delete ?right_id_L ?lookup_singleton /=;
      destruct w; destruct u; done.
  Qed.

  Lemma wp_load_graph g markings k q (x : loc) u w :
    (g !! x) = Some u →
    (graph_ctx κ g markings ∗ own_graph q (x [↦] w) ∗ cinv_own κ k)
      ⊢
      WP (! #x)
      {{ v, (∃ m : loc, ⌜markings !! x = Some m⌝ ∧
              ⌜v = (#m, children_to_val w)⌝%V) ∗ ⌜strict_sub_children u w⌝
              ∗ own_graph q (x [↦] w) ∗ cinv_own κ k }}.
  Proof.
    iIntros (Hgx) "(#Hgr & Hx & key)".
    assert (Hgx' : x ∈ dom g).
    { rewrite elem_of_dom Hgx; eauto. }
    unfold graph_ctx.
    iMod (cinv_acc _ graphN with "Hgr key")
      as "(>Hinv & key & Hclose)"; first done.
    unfold graph_inv at 2.
    iDestruct "Hinv" as (G) "(Hi1 & Hi2 & Hi3 & Hi4)".
    iDestruct (graph_open with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    iDestruct "Hil" as (u') "[Hil1 Hil2]".
    iDestruct "Hil2" as (m) "[Hil2 [Hil3 Hil4]]".
    wp_load. iDestruct "Hil1" as %Hil1.
    iDestruct "Hil2" as %Hil2. iDestruct "Hi4" as %Hi4.
    iDestruct (auth_own_graph_valid with "Hi1") as %Hvl.
    iDestruct (graph_pointsto_marked with "[Hi1 Hx]")
      as %Heq; try by iFrame.
    pose proof Hil1 as Hil1'. rewrite Heq in Hil1' Hvl.
    rewrite mark_update_lookup in Hil1'; trivial.
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3"; [by iFrame|].
    iMod ("Hclose" with "[Hi1 Hi2 Hi3]") as "_".
    { iNext. unfold graph_inv at 2. iExists _; iFrame; auto. }
    iFrame. inversion Hil1'; subst u'; simpl.
    iModIntro. iSplit.
    - iExists _; iSplit; iPureIntro; eauto.
    - iPureIntro. rewrite Heq in Hi4. eapply laod_strict_sub_children; eauto.
  Qed.

  Lemma wp_store_graph {g markings k q} {x : loc} {v}
        (w w' : option loc * option loc) {m : loc} :
    strict_sub_children w w' → (markings !! x) = Some m →
      (g !! x) = Some v →
      (graph_ctx κ g markings ∗ own_graph q (x [↦] w) ∗ cinv_own κ k)
        ⊢
        WP (#x <- (#m, children_to_val w')%V)
        {{ v, own_graph q (x [↦] w') ∗ cinv_own κ k }}.
  Proof.
    iIntros (Hagree Hmrk Hgx) "(#Hgr & Hx & key)".
    assert (Hgx' : x ∈ dom g).
    { rewrite elem_of_dom Hgx; eauto. }
    unfold graph_ctx. wp_pures.
    iMod (cinv_acc _ graphN with "Hgr key")
      as "(>Hinv & key & Hclose)"; first done.
    unfold graph_inv at 2.
    iDestruct "Hinv" as (G) "(Hi1 & Hi2 & Hi3 & Hi4)".
    iDestruct (graph_open with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    iDestruct "Hil" as (u') "[Hil1 Hil2]".
    iDestruct "Hil2" as (m') "[Hil2 [Hil3 Hil4]]".
    wp_store.
    iDestruct "Hil2" as %Hil2.
    rewrite Hmrk in Hil2. inversion Hil2; subst; clear Hil2.
    iDestruct "Hil1" as %Hil1. iDestruct "Hi4" as %Hi4.
    iDestruct (auth_own_graph_valid with "Hi1") as %Hvl.
    iDestruct (graph_pointsto_marked with "[Hi1 Hx]") as %Heq; try by iFrame.
    pose proof Hil1 as Hil1'. rewrite Heq in Hil1' Hvl Hi4.
    rewrite mark_update_lookup in Hil1'; trivial. inversion Hil1'; subst u'.
    clear Hil1'. simpl. rewrite Heq.
    iMod (update_graph _ _ _ w' with "[Hi1 Hx]") as
        "[Hi1 Hx]"; try by iFrame.
    { by rewrite lookup_delete. }
    rewrite -delete_marked. erewrite (delete_marked _ _ _ w').
    assert (HvG : ✓ ({[x := Excl w']} ⋅ delete x G)).
    { eapply update_valid; eauto. }
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3".
    { iFrame. iExists _. iSplitR.
      - rewrite ?mark_update_lookup; eauto. - iExists _; by iFrame. }
    iMod ("Hclose" with "[Hi1 Hi2 Hi3]") as "_"; [|by iFrame].
    unfold graph_inv at 2.
    iNext. iExists _; iFrame. rewrite !dom_op !dom_singleton_L. iFrame.
    iPureIntro.
    { eapply update_strict_subgraph; eauto. }
  Qed.

  Lemma wp_unmark_fst g markings k q (x : loc) v w1 w2 :
    (g !! x) = Some v →
    (graph_ctx κ g markings ∗ own_graph q (x [↦] (w1, w2))
     ∗ cinv_own κ k) ⊢
      WP (unmark_fst #x)
      {{ _, own_graph q (x [↦] (None, w2)) ∗ cinv_own κ k }}.
  Proof.
    iIntros (Hgx) "(#Hgr & Hx & key)".
    wp_lam. wp_bind (! _)%E.
    iApply wp_wand_l; iSplitR;
      [|iApply wp_load_graph; eauto; iFrame "Hgr"; by iFrame].
    iIntros (u) "(H1 & Hagree & Hx & key)". iDestruct "H1" as (m) "[Hmrk Hu]".
    iDestruct "Hagree" as %Hagree.
    iDestruct "Hmrk" as %Hmrk; iDestruct "Hu" as %Hu; subst.
    wp_pures.
    iApply (wp_store_graph _ (None, w2) with "[Hx key]"); eauto;
      [|iFrame "Hgr"; by iFrame].
    { by destruct w1; destruct w2; destruct v; inversion Hagree; subst. }
  Qed.

  Lemma wp_unmark_snd g markings k q (x : loc) v w1 w2 :
    (g !! x) = Some v →
    (graph_ctx κ g markings ∗ own_graph q (x [↦] (w1, w2))
     ∗ cinv_own κ k) ⊢
      WP (unmark_snd #x)
      {{ _, own_graph q (x [↦] (w1, None)) ∗ cinv_own κ k }}.
  Proof.
    iIntros (Hgx) "(#Hgr & Hx & key)".
    wp_lam. wp_bind (! _)%E.
    iApply wp_wand_l; iSplitR;
      [|iApply wp_load_graph; eauto; iFrame "Hgr"; by iFrame].
    iIntros (u) "(H1 & Hagree & Hx & key)". iDestruct "H1" as (m) "[Hmrk Hu]".
    iDestruct "Hagree" as %Hagree.
    iDestruct "Hmrk" as %Hmrk; iDestruct "Hu" as %Hu; subst.
    wp_pures.
    iApply (wp_store_graph _ (w1, None) with "[Hx key]"); eauto;
      [|iFrame "Hgr"; by iFrame].
    { by destruct w1; destruct w2; destruct v; inversion Hagree; subst. }
  Qed.

  Lemma front_op (g : graph loc) (G G' : Gmon) (t : gset loc) :
    front g (dom G) t → front g (dom G') t →
    front g (dom (G ⋅ G')) t.
  Proof.
    rewrite dom_op. intros [HGd HGf] [HGd' HGf']; split.
    - intros x; rewrite elem_of_union; intuition.
    - intros x y; rewrite elem_of_union; intuition eauto.
  Qed.
  Lemma front_singleton (g : graph loc) (t : gset loc) l (w : chlO) u1 u2 :
    g !! l = Some (u1, u2) →
    match u1 with |Some l1 => l1 ∈ t | None => True end →
    match u2 with |Some l2 => l2 ∈ t | None => True end →
    front g (dom (l [↦] w : gmap loc _)) t.
  Proof.
    intros Hgl Hu1 Hu2.
    split => [x |x y]; rewrite ?dom_singleton ?elem_of_singleton => ?; subst.
    - rewrite elem_of_dom Hgl; eauto.
    - rewrite /get_left /get_right Hgl /=.
      destruct u1; destruct u2; simpl; intros [Heq|Heq]; by inversion Heq; subst.
  Qed.
  Lemma empty_graph_divide q :
    own_graph q ∅ ⊢ own_graph (q / 2) ∅ ∗ own_graph (q / 2) ∅.
  Proof.
    setoid_replace (∅ : gmapR loc (exclR chlO)) with
    (∅ ⋅ ∅ : gmapR loc (exclR chlO)) at 1 by (by rewrite ucmra_unit_left_id).
    by rewrite graph_divide.
  Qed.

  Lemma front_marked (g : graph loc) (l : loc) u1 u2 w mr1 mr2 (G1 G2 : Gmon) :
    g !! l = Some (u1, u2) →
    (front g (dom G1) mr1) → (front g (dom G2) mr2) →
    ([∗ set] l ∈ mr1, is_marked l) ∗ ([∗ set] l ∈ mr2, is_marked l) ∗
    match u1 with |Some l1 => is_marked l1 | None => True end ∗
    match u2 with |Some l2 => is_marked l2 | None => True end ⊢
    ∃ (mr : gset loc), ⌜front g (dom ((l [↦] w) ⋅ (G1 ⋅ G2))) mr⌝
      ∗ ([∗ set] l ∈ mr, is_marked l).
  Proof.
    iIntros (Hgl Hfr1 Hfr2) "(Hmr1 & Hmr2 & Hu1 & Hu2)".
    iExists (match u1 with |Some l1 => {[l1]} | None => ∅ end ∪
             match u2 with |Some l2 => {[l2]} | None => ∅ end ∪ mr1 ∪ mr2).
    iSplitR; [iPureIntro|].
    - repeat apply front_op.
      + eapply front_singleton; eauto; simpl; destruct u1; destruct u2; trivial;
           rewrite ?elem_of_union ?elem_of_singleton; intuition.
      + eapply front_mono; eauto => x. rewrite ?elem_of_union; intuition.
      + eapply front_mono; eauto => x. rewrite ?elem_of_union; intuition.
    - rewrite ?big_sepS_forall. iIntros (x); destruct u1; destruct u2;
        rewrite ?elem_of_union ?elem_of_empty ?elem_of_singleton; iIntros (Hx);
        intuition; subst; auto; solve [iApply "Hmr1"; auto|iApply "Hmr2"; auto].
  Qed.

  Lemma rec_wp_span g markings k q (x : val) :
    maximal g →
    (x = NONEV ∨ ∃ l : loc,
        x = SOMEV #l ∧ l ∈ dom g) →
    (graph_ctx κ g markings ∗ own_graph q ∅ ∗ cinv_own κ k)
      ⊢
      WP (span x)
      {{ v, ((⌜v = # true⌝ ∗
             (∃ l : loc, ⌜x = SOMEV #l⌝ ∗
               (∃ (G : Gmon) mr (tr : tree (Gmon_graph G) l),
                  own_graph q G ∗ ⌜l ∈ dom G⌝ ∗
                  ⌜maximal (Gmon_graph G)⌝ ∗ ⌜front g (dom G) mr⌝ ∗
                   ([∗ set] l ∈ mr , is_marked l)) ∗ is_marked l)) ∨
             (⌜v = # false⌝ ∗
              (⌜x = NONEV⌝ ∨ (∃ l : loc, ⌜x = SOMEV #l⌝ ∗ is_marked l))
               ∗ own_graph q ∅))
            ∗ cinv_own κ k
      }}.
  Proof using Type*.
    intros [_ Hgmx] Hxpt. iIntros "(#Hgr & Hx & key)".
    iRevert (x Hxpt k q) "key Hx". iLöb as "IH".
    iIntros (x Hxpt k q) "key Hx".
    wp_rec.
    destruct Hxpt as [|[l [? Hgsl]]]; subst.
    { wp_match. iModIntro.
      iFrame; iRight; iFrame; repeat iSplit; trivial; by iLeft. }
    wp_match. wp_bind (try_mark _).
    iDestruct (empty_graph_divide with "Hx") as "[Hx1 Hx2]".
    iApply wp_wand_l; iSplitL "Hx1";
      [|iApply wp_try_mark; try iFrame]; eauto; simpl.
    iIntros (v) "[(% & Hv & Hm & key)|(% & Hx2 & Hm & key)]"; subst;
    [|iCombine "Hx1" "Hx2" as "Hx"; rewrite -graph_divide ucmra_unit_right_id;
      wp_if; iModIntro; iFrame; iRight; iFrame; iSplit; trivial; iRight;
      iExists _; eauto].
    iDestruct "Hv" as (u) "[Hgl Hl]". iDestruct "Hgl" as %Hgl.
    wp_if.
    (* reading the reference. This part is very similar to unmark lemmas! *)
    wp_bind (! _)%E.
    iApply wp_wand_l; iSplitR "Hl key";
      [|iApply wp_load_graph; eauto; iFrame "Hgr"; by iFrame].
    iIntros (v) "(H1 & Hagree & Hx & key)". iDestruct "H1" as (m) "[Hmrk Hv]".
    iDestruct "Hagree" as %Hagree. iDestruct "Hv" as %Hv; subst v.
    wp_let. wp_pures. wp_bind (par _ _).
    iDestruct "key" as "[K1 K2]".
    iDestruct (empty_graph_divide with "Hx1") as "[Hx11 Hx12]".
    destruct u as [u1 u2]. iApply (par_spec with "[Hx11 K1] [Hx12 K2]").
    { (* symbolically executing the left part of the par. *)
      wp_lam; repeat wp_proj.
      iApply ("IH" $! (child_to_val u1) with "[%] K1 Hx11").
      destruct u1 as [l1|]; [right |by left].
      exists l1; split; trivial. eapply (Hgmx l); rewrite // /get_left Hgl; auto. }
    { (* symbolically executing the left part of the par. *)
      wp_lam; repeat wp_proj.
      iApply ("IH" with "[%] K2 Hx12"); auto.
      destruct u2 as [l2|]; [right |by left].
      exists l2; split; trivial. eapply (Hgmx l); rewrite // /get_right Hgl; auto. }
    (* continuing after both children are processed *)
    iNext.
    iIntros (vl vr) "([Hvl K1] & Hvr & K2 & K2')".
    iCombine "K2" "K2'" as "K2". iCombine "K1" "K2" as "key".
    iNext. wp_let.
    (* We don't need the huge induction hypothesis anymore. *)
    iClear "IH".
    (* separating all four cases *)
    iDestruct "Hvl" as "[[% Hvll]|[% Hvlr]]"; subst;
      iDestruct "Hvr" as "[[% Hvrl]|[% Hvrr]]"; subst.
    - wp_pures.
      iDestruct "Hvll" as (l1) "(Hl1eq & Hg1 & ml1)".
      iDestruct "Hg1" as (G1 mr1 tr1) "(Hxl & Hl1im & Hmx1 & Hfr1 & Hfml)".
      iDestruct "Hfr1" as %Hfr1. iDestruct "Hmx1" as %Hmx1.
      iDestruct "Hl1eq" as %Hl1eq. iDestruct "Hl1im" as %Hl1im.
      iDestruct "Hvrl" as (l2) "(Hl2eq & Hg2 & ml2)".
      iDestruct "Hg2" as (G2 mr2 tr2) "(Hxr & Hl2im & Hmx2 & Hfr2 & Hfmr)".
      iDestruct "Hfr2" as %Hfr2. iDestruct "Hmx2" as %Hmx2.
      iDestruct "Hl2eq" as %Hl2eq. iDestruct "Hl2im" as %Hl2im.
      iCombine "Hxl" "Hxr" as "Hxlr". rewrite -graph_divide.
      iCombine "Hx" "Hxlr" as "Hx". rewrite -graph_divide.
      destruct u1; destruct u2; inversion Hl1eq; inversion Hl2eq; subst.
      iModIntro. iFrame; iLeft. iSplit; [trivial|].
      iExists _; iSplit; [trivial|]. iFrame "Hm".
      iDestruct (own_graph_valid with "Hx") as %Hvl. iFrame "Hx".
      iDestruct (front_marked _ _ _ _ (Some l1, Some l2) _ _ G1 G2 with
      "[ml1 ml2 Hfml Hfmr]") as (mr)"[Hfr Hfm]"; eauto. iDestruct "Hfr" as %Hfr.
      iFrame "Hfm".
      unshelve iExists _; [eapply maximally_marked_tree_both; eauto|].
      iSplit; try iPureIntro; eauto.
      { rewrite dom_op dom_singleton elem_of_union elem_of_singleton; by left. }
      split; auto.
      { eapply maximally_marked_tree_both; eauto. }
    - wp_pures.
      iDestruct "Hvll" as (l1) "(Hl1eq & Hg1 & ml1)".
      iDestruct "Hg1" as (G1 mr1 tr1) "(Hxl & Hl1im & Hmx1 & Hfr1 & Hfml)".
      iDestruct "Hfr1" as %Hfr1. iDestruct "Hmx1" as %Hmx1.
      iDestruct "Hl1eq" as %Hl1eq. iDestruct "Hl1im" as %Hl1im.
      iDestruct "Hvrr" as "(Hvr & Hxr)".
      iCombine "Hxl" "Hxr" as "Hxlr". rewrite -graph_divide ucmra_unit_right_id.
      wp_bind (unmark_snd _).
      iApply wp_wand_l; iSplitR "Hx key";
        [|iApply wp_unmark_snd; eauto; by iFrame "Hgr"; iFrame].
      iIntros (v) "[Hx key]".
      iCombine "Hx" "Hxlr" as "Hx". rewrite -graph_divide.
      wp_seq. iModIntro.
      iFrame; iLeft. iSplit; [trivial|].
      iExists _; iSplit; [trivial|]. iFrame "Hm".
      iDestruct (own_graph_valid with "Hx") as %Hvld. iFrame "Hx".
      destruct u1; inversion Hl1eq; subst.
      iDestruct (front_marked _ _ _ _ (Some l1, None) _ ∅ G1 ∅ with
      "[ml1 Hvr Hfml]") as (mr)"[Hfr Hfm]"; eauto.
      { rewrite dom_empty_L; apply front_empty. }
      { rewrite big_sepS_empty. iFrame.
        destruct u2; iDestruct "Hvr" as "[Hvr|Hvr]"; trivial;
        [iDestruct "Hvr" as %Hvr; inversion Hvr|
         iDestruct "Hvr" as (l2) "[Hvreq Hvr]"; iDestruct "Hvreq" as %Hvreq;
         by inversion Hvreq]. }
      iDestruct "Hfr" as %Hfr. rewrite right_id_L in Hfr. iFrame "Hfm".
      unshelve iExists _; [eapply maximally_marked_tree_left; eauto|].
      iSplit; try iPureIntro; eauto.
      { rewrite dom_op dom_singleton elem_of_union elem_of_singleton; by left. }
      split; auto.
      { eapply maximally_marked_tree_left; eauto. }
    - wp_pures.
      iDestruct "Hvlr" as "(Hvl & Hxl)".
      iDestruct "Hvrl" as (l2) "(Hl2eq & Hg2 & ml2)".
      iDestruct "Hg2" as (G2 mr2 tr2) "(Hxr & Hl2im & Hmx2 & Hfr2 & Hfmr)".
      iDestruct "Hfr2" as %Hfr2. iDestruct "Hmx2" as %Hmx2.
      iDestruct "Hl2eq" as %Hl2eq. iDestruct "Hl2im" as %Hl1im.
      iCombine "Hxl" "Hxr" as "Hxlr". rewrite -graph_divide left_id.
      wp_bind (unmark_fst _).
      iApply wp_wand_l; iSplitR "Hx key";
        [|iApply wp_unmark_fst; eauto; by iFrame "Hgr"; iFrame].
      iIntros (v) "[Hx key]".
      iCombine "Hx" "Hxlr" as "Hx". rewrite -graph_divide.
      wp_seq. wp_proj. wp_op. wp_if. wp_seq. iModIntro.
      iFrame; iLeft. iSplit; [trivial|].
      iExists _; iSplit; [trivial|]. iFrame "Hm".
      iDestruct (own_graph_valid with "Hx") as %Hvld. iFrame "Hx".
      destruct u2; inversion Hl2eq; subst.
      iDestruct (front_marked _ _ _ _ (None, Some l2) ∅ _ ∅ G2 with
      "[ml2 Hvl Hfmr]") as (mr)"[Hfr Hfm]"; eauto.
      { rewrite dom_empty_L; apply front_empty. }
      { rewrite big_sepS_empty. iFrame.
        destruct u1; iDestruct "Hvl" as "[Hvl|Hvl]"; trivial;
        [iDestruct "Hvl" as %Hvl; inversion Hvl|
         iDestruct "Hvl" as (l1) "[Hvleq Hvl]"; iDestruct "Hvleq" as %Hvleq;
         by inversion Hvleq]. }
      iDestruct "Hfr" as %Hfr. rewrite left_id_L in Hfr.
      iFrame "Hfm".
      unshelve iExists _; [eapply maximally_marked_tree_right; eauto|].
      iSplit; try iPureIntro; eauto.
      { rewrite dom_op dom_singleton elem_of_union elem_of_singleton; by left. }
      split; auto.
      { eapply maximally_marked_tree_right; eauto. }
    - iDestruct "Hvlr" as "(Hvl & Hxl)".
      iDestruct "Hvrr" as "(Hvr & Hxr)".
      iCombine "Hxl" "Hxr" as "Hxlr". rewrite -graph_divide ucmra_unit_right_id.
      wp_proj. wp_op. wp_if. wp_bind(unmark_fst _).
      iApply wp_wand_l; iSplitR "Hx key";
        [|iApply wp_unmark_fst; eauto; by iFrame "Hgr"; iFrame].
      iIntros (v) "[Hx key]".
      wp_seq. wp_proj. wp_op. wp_if. wp_bind(unmark_snd _).
      iApply wp_wand_l; iSplitR "Hx key";
        [|iApply wp_unmark_snd; eauto; by iFrame "Hgr"; iFrame].
      clear v. iIntros (v) "[Hx key]".
      iCombine "Hx" "Hxlr" as "Hx". rewrite -graph_divide.
      wp_seq. iModIntro.
      iFrame; iLeft. iSplit; [trivial|].
      iExists _; iSplit; [trivial|]. iFrame "Hm".
      iDestruct (own_graph_valid with "Hx") as %Hvld. iFrame "Hx".
      iDestruct (front_marked _ _ _ _ (None, None) ∅ ∅ ∅ ∅ with
      "[Hvr Hvl]") as (mr)"[Hfr Hfm]"; eauto.
      { rewrite dom_empty_L; apply front_empty. }
      { rewrite dom_empty_L; apply front_empty. }
      { rewrite big_sepS_empty.
        destruct u1; iDestruct "Hvl" as "[Hvl|Hvl]";
          destruct u2; iDestruct "Hvr" as "[Hvr|Hvr]";
          try (iDestruct "Hvl" as %Hvl; inversion Hvl);
          try (iDestruct "Hvr" as %Hvr; inversion Hvr);
          try (iDestruct "Hvl" as (ll) "[Hvleq Hvl]";
            iDestruct "Hvleq" as %Hvleq; inversion Hvleq);
          try (iDestruct "Hvr" as (lr) "[Hvreq Hvr]";
            iDestruct "Hvreq" as %Hvreq; inversion Hvreq);
          iFrame; by repeat iSplit. }
      iDestruct "Hfr" as %Hfr. rewrite left_id_L in Hfr.
      iFrame "Hfm".
      rewrite right_id_L. rewrite right_id_L in Hvld Hfr.
      unshelve iExists _; [eapply maximally_marked_tree_none; eauto|].
      iSplit; try iPureIntro; eauto.
      { by rewrite dom_singleton elem_of_singleton. }
      split; auto.
      { eapply maximally_marked_tree_none; eauto. }
  Qed.

End Helpers.
