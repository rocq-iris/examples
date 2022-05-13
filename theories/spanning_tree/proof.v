From iris.algebra Require Import frac gmap auth.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
From iris.base_logic Require Import cancelable_invariants.
From iris.prelude Require Import options.

From iris_examples.spanning_tree Require Import graph mon spanning.

Section wp_span.
  Context `{heapGS Σ, cinvG Σ, inG Σ (authR markingUR),
            inG Σ (authR graphUR), spawnG Σ}.

  Lemma wp_span g (markings : gmap loc loc) (x : val) (l : loc) :
    l ∈ dom g → maximal g → connected g l →
    ([∗ map] l ↦ v ∈ g,
       ∃ (m : loc), ⌜markings !! l = Some m⌝ ∗ l ↦ (#m, children_to_val v)
         ∗ m ↦ #false) ⊢
      WP span (SOME #l)
      {{ _, ∃ g',
              ([∗ map] l ↦ v ∈ g',
                ∃ m : loc, ⌜markings !! l = Some m⌝ ∗ l ↦ (#m, children_to_val v)
                  ∗ m ↦ #true)
             ∗ ⌜dom g = dom g'⌝
             ∗ ⌜strict_subgraph g g'⌝ ∗ ⌜tree g' l⌝
      }}.
  Proof using Type*.
    iIntros (Hgl Hgmx Hgcn) "Hgr".
    iMod (graph_ctx_alloc _ g markings with "[Hgr]") as (Ig κ) "(key & #Hgr & Hg)";
      eauto.
    iApply wp_fupd. wp_pures.
    iApply wp_wand_l; iSplitR;
      [|iApply ((rec_wp_span κ g markings 1 1 (SOMEV #l)) with "[Hg key]");
        eauto; iFrame "#"; iFrame].
    iIntros (v) "[H key]".
    unfold graph_ctx.
    iMod (cinv_cancel ⊤ graphN κ (graph_inv g markings) with "[#] [key]")
      as ">Hinv"; first done; try by iFrame.
    iClear "Hgr". unfold graph_inv.
    iDestruct "Hinv" as (G) "(Hi1 & Hi2 & Hi3 & Hi4)".
    iDestruct "Hi4" as %Hi4.
    iDestruct "H" as "[H|H]".
    - iDestruct "H" as "(_ & H)". iDestruct "H" as (l') "(H1 & H2 & Hl')".
      iDestruct "H1" as %Hl; inversion Hl; subst.
      iDestruct "H2" as (G' gmr gtr) "(Hl1 & Hl2 & Hl3 & Hl4 & Hl5)".
      iDestruct "Hl2" as %Hl2. iDestruct "Hl3" as %Hl3. iDestruct "Hl4" as %Hl4.
      iDestruct (whole_frac with "[Hi1 Hl1]") as %Heq; [by iFrame|]; subst.
      iDestruct (marked_is_marked_in_auth_sepS with "[Hi2 Hl5]") as %Hmrk;
        [by iFrame|].
      iDestruct (own_graph_valid with "Hl1") as %Hvl.
      iExists (Gmon_graph G').
      assert (dom g = dom (Gmon_graph G')).
      { erewrite front_t_t_dom; eauto.
        - by rewrite Gmon_graph_dom.
        - eapply front_mono; rewrite Gmon_graph_dom; eauto. }
      iModIntro. repeat iSplitL; try by iPureIntro.
      rewrite /heap_owns of_graph_dom_eq //=. by rewrite big_sepM_fmap /=.
    - iDestruct "H" as "(_ & [H|H] & Hx)".
      + iDestruct "H" as %Heq. inversion Heq.
      + iDestruct "H" as (l') "(_ & Hl)".
        iDestruct (marked_is_marked_in_auth with "[Hi2 Hl]") as %Hmrk;
          [by iFrame|].
        iDestruct (whole_frac with "[Hx Hi1]") as %Heq; [by iFrame|]; subst.
        exfalso; revert Hmrk. rewrite dom_empty. inversion 1.
  Qed.

End wp_span.
