From stdpp Require Import gmap mapset.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import auth frac gset gmap excl.
From iris.base_logic Require Export invariants.
From iris.base_logic Require Import cancelable_invariants.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

From iris_examples.spanning_tree Require Import graph.

(* children cofe *)
Canonical Structure chlO := leibnizO (option loc * option loc).
(* The graph monoid. *)
Definition graphN : namespace := nroot .@ "SPT_graph".
Definition graphUR : ucmra :=
  optionUR (prodR fracR (gmapR loc (exclR chlO))).
(* The monoid for talking about which nodes are marked.
These markings are duplicatable. *)
Definition markingUR : ucmra := gsetUR loc.

(** The CMRA we need. *)
Class graphG Σ := GraphG
  {
    graph_marking_inG :: inG Σ (authR markingUR);
    graph_marking_name : gname;
    graph_inG :: inG Σ (authR graphUR);
    graph_name : gname
  }.
(** The Functor we need. *)
(*Definition graphΣ : gFunctors := #[authΣ graphUR].*)

Section marking_definitions.
  Context `{irisGS heap_lang Σ, graphG Σ}.

  Definition is_marked (l : loc) : iProp Σ :=
    own graph_marking_name (◯ {[ l ]}).

  Global Instance marked_persistentP x : Persistent (is_marked x).
  Proof. apply _. Qed.

  Lemma dup_marked l : is_marked l ⊣⊢ is_marked l ∗ is_marked l.
  Proof.  by rewrite /is_marked -own_op -auth_frag_op idemp_L. Qed.

  Lemma new_marked {E} (m : markingUR) l :
  own graph_marking_name (● m) ={E}=∗
  own graph_marking_name (● (m ⋅ ({[l]} : gset loc))) ∗ is_marked l.
  Proof.
    iIntros "H". rewrite -own_op (comm _ m).
    iMod (own_update with "H") as "Y"; eauto.
    apply auth_update_alloc.
    setoid_replace ({[l]} : gset loc) with (({[l]} : gset loc) ⋅ ∅) at 2
      by (by rewrite right_id).
    apply op_local_update_discrete; auto.
  Qed.

  Lemma already_marked {E} (m : gset loc) l : l ∈ m →
    own graph_marking_name (● m) ={E}=∗
    own graph_marking_name (● m) ∗ is_marked l.
  Proof.
    iIntros (Hl) "Hm". iMod (new_marked with "Hm") as "[H1 H2]"; iFrame.
    rewrite gset_op (comm _ m) (subseteq_union_1_L {[l]} m); trivial.
    by apply elem_of_subseteq_singleton.
  Qed.

End marking_definitions.

(* The monoid representing graphs *)
Definition Gmon := gmapR loc (exclR chlO).

Definition excl_chlC_chl (ch : exclR chlO) : option (option loc * option loc) :=
  match ch with
  | Excl w => Some w
  | ExclInvalid => None
  end.

Definition Gmon_graph (G : Gmon) : graph loc := omap excl_chlC_chl G.

Definition Gmon_graph_dom (G : Gmon) :
  ✓ G → dom (Gmon_graph G) = dom G.
Proof.
  intros Hvl; apply set_eq=> i. rewrite !elem_of_dom lookup_omap.
  specialize (Hvl i). split.
  - revert Hvl; case _ : (G !! i) => [[]|] //=; eauto.
    intros _ [? Hgi]; inversion Hgi.
  - intros Hgi; revert Hgi Hvl. intros [[] Hgi]; rewrite Hgi; inversion 1; eauto.
Qed.

Definition child_to_val (c : option loc) : val :=
  match c with
  | None => NONEV
  | Some l => SOMEV #l
  end.

(* convert the data of a node to a value in the heap *)
Definition children_to_val (ch : option loc * option loc) : val :=
  (child_to_val (ch.1), child_to_val (ch.2)).

Definition marked_graph := gmap loc (bool * (option loc * option loc)).
Identity Coercion marked_graph_gmap: marked_graph >-> gmap.

Definition of_graph_elem (G : Gmon) i v
  : option (bool * (option loc * option loc)) :=
  match Gmon_graph G !! i with
  | Some w => Some (true, w)
  | None => Some (false,v)
  end.

Definition of_graph (g : graph loc) (G : Gmon) : marked_graph :=
  map_imap (of_graph_elem G) g.

(* facts *)

Global Instance Gmon_graph_proper : Proper ((≡) ==> (=)) Gmon_graph.
Proof. solve_proper. Qed.

Lemma new_Gmon_dom (G : Gmon) x w :
  dom (G ⋅ {[x := w]}) = dom G ∪ {[x]}.
Proof. by rewrite dom_op dom_singleton_L. Qed.

Definition of_graph_empty (g : graph loc) :
  of_graph g ∅ = fmap (λ x, (false, x)) g.
Proof.
  apply: map_eq => i.
  rewrite map_lookup_imap /of_graph_elem lookup_fmap lookup_omap //.
Qed.

Lemma of_graph_dom_eq g G :
  ✓ G → dom g = dom (Gmon_graph G) →
  of_graph g G = fmap (λ x, (true, x) )(Gmon_graph G).
Proof.
  intros HGvl. rewrite Gmon_graph_dom // => Hd. apply map_eq => i.
  assert (Hd' : i ∈ dom g ↔ i ∈ dom G) by (by rewrite Hd).
  revert Hd'; clear Hd. specialize (HGvl i); revert HGvl.
  rewrite /of_graph /of_graph_elem /Gmon_graph map_lookup_imap lookup_fmap
    lookup_omap ?elem_of_dom.
  case _ : (g !! i); case _ : (G !! i) => [[]|] /=; inversion 1; eauto;
    intros [? ?];
    match goal with
      H : _ → @is_Some ?A None |- _ =>
       assert (Hcn : @is_Some A None) by eauto;
         destruct Hcn as [? Hcn]; inversion Hcn
    end.
Qed.

Section definitions.
  Context `{heapGS Σ, graphG Σ}.

  Definition own_graph (q : frac) (G : Gmon) : iProp Σ :=
    own graph_name (◯ (Some (q, G) : graphUR)).

  Global Instance own_graph_proper q : Proper ((≡) ==> (⊣⊢)) (own_graph q).
  Proof. solve_proper. Qed.

  Definition heap_owns (M : marked_graph) (markings : gmap loc loc) : iProp Σ :=
    ([∗ map] l ↦ v ∈ M, ∃ (m : loc), ⌜markings !! l = Some m⌝
       ∗ l ↦ (#m, children_to_val (v.2)) ∗ m ↦ #(LitBool (v.1)))%I.

  Definition graph_inv (g : graph loc) (markings : gmap loc loc) : iProp Σ :=
    (∃ (G : Gmon), own graph_name (● Some (1%Qp, G))
      ∗ own graph_marking_name (● dom G)
      ∗ heap_owns (of_graph g G) markings ∗ ⌜strict_subgraph g (Gmon_graph G)⌝
    )%I.

  Global Instance graph_inv_timeless g Mrk : Timeless (graph_inv g Mrk).
  Proof. apply _. Qed.

  Context `{cinvG Σ}.
  Definition graph_ctx κ g Mrk : iProp Σ := cinv graphN κ (graph_inv g Mrk).

  Global Instance graph_ctx_persistent κ g Mrk : Persistent (graph_ctx κ g Mrk).
  Proof. apply _. Qed.

End definitions.

Notation "l [↦] v" := ({[l := Excl v]}) (at level 70, format "l  [↦]  v").

Global Typeclasses Opaque graph_ctx graph_inv own_graph.

Section graph_ctx_alloc.
  Context `{heapGS Σ, cinvG Σ, inG Σ (authR markingUR), inG Σ (authR graphUR)}.

  Lemma graph_ctx_alloc (E : coPset) (g : graph loc) (markings : gmap loc loc)
        (HNE : (nclose graphN) ⊆ E)
  : ([∗ map] l ↦ v ∈ g, ∃ (m : loc), ⌜markings !! l = Some m⌝
       ∗ l ↦ (#m, children_to_val v) ∗ m ↦ #false)
     ={E}=∗ ∃ (Ig : graphG Σ) (κ : gname), cinv_own κ 1 ∗ graph_ctx κ g markings
             ∗ own_graph 1%Qp ∅.
  Proof using Type*.
    iIntros "H1".
    iMod (own_alloc (● (∅ : markingUR))) as (mn) "H2"; first by apply auth_auth_valid.
    iMod (own_alloc (● (Some (1%Qp, ∅ : Gmon) : graphUR)
                      ⋅ ◯ (Some (1%Qp, ∅ : Gmon) : graphUR))) as (gn) "H3".
    { by apply auth_both_valid_discrete. }
    iDestruct "H3" as "[H31 H32]".
    set (Ig := GraphG _ _ mn _ gn).
    iExists Ig.
    iAssert (graph_inv g markings) with "[H1 H2 H31]" as "H".
    { unfold graph_inv. iExists ∅. rewrite dom_empty_L. iFrame "H2 H31".
      iSplitL; [|iPureIntro].
      - rewrite /heap_owns of_graph_empty  big_sepM_fmap; eauto.
      - rewrite /Gmon_graph omap_empty; apply strict_subgraph_empty. }
    iMod (cinv_alloc _ graphN with "[H]") as (κ) "[Hinv key]".
    { iNext. iExact "H". }
    iExists κ.
    rewrite /own_graph /graph_ctx //=; by iFrame.
  Qed.

End graph_ctx_alloc.

Lemma marked_was_unmarked (G : Gmon) x v :
  ✓ ({[x := Excl v]} ⋅ G) → G !! x = None.
Proof.
  intros H2; specialize (H2 x).
  revert H2; rewrite lookup_op lookup_singleton. intros H2.
    by rewrite (excl_validN_inv_l O _ _ (proj1 (cmra_valid_validN _) H2 O)).
Qed.

Lemma mark_update_lookup_base (G : Gmon) x v :
  ✓ ({[x := Excl v]} ⋅ G) → ({[x := Excl v]} ⋅ G) !! x = Some (Excl v).
Proof.
  intros H2; rewrite lookup_op lookup_singleton.
  erewrite marked_was_unmarked; eauto.
Qed.

Lemma mark_update_lookup_ne_base (G : Gmon) x i v :
  i ≠ x → ({[x := Excl v]} ⋅ G) !! i = G !! i.
Proof. intros H. by rewrite lookup_op lookup_singleton_ne //= left_id_L. Qed.

Lemma of_graph_dom g G : dom (of_graph g G) = dom g.
Proof.
  apply set_eq=>i.
  rewrite ?elem_of_dom map_lookup_imap /of_graph_elem lookup_omap.
  case _ : (g !! i) => [x|]; case _ : (G !! i) => [[]|] //=; split;
  intros [? Hcn]; inversion Hcn; eauto.
Qed.

Lemma in_dom_of_graph (g : graph loc) (G : Gmon) x (b : bool) v :
  ✓ G → of_graph g G !! x = Some (b, v) → b ↔ x ∈ dom G.
Proof.
  rewrite /of_graph /of_graph_elem map_lookup_imap lookup_omap elem_of_dom.
  intros Hvl; specialize (Hvl x); revert Hvl;
  case _ : (g !! x) => [?|]; case _ : (G !! x) => [[] ?|] //=;
    intros Hvl; inversion Hvl; try (inversion 1; subst); split;
    try (inversion 1; fail); try (intros [? Hcn]; inversion Hcn; fail);
    subst; eauto.
Qed.

Global Instance of_graph_proper g : Proper ((≡) ==> (=)) (of_graph g).
Proof. solve_proper. Qed.


Lemma mark_update_lookup (g : graph loc) (G : Gmon) x v :
  x ∈ dom g →
  ✓ ((x [↦] v) ⋅ G) → of_graph g ((x [↦] v) ⋅ G) !! x = Some (true, v).
Proof.
  rewrite elem_of_dom /is_Some. intros [w H1] H2.
  rewrite /of_graph /of_graph_elem map_lookup_imap H1 lookup_omap; simpl.
  rewrite mark_update_lookup_base; trivial.
Qed.

Lemma mark_update_lookup_ne (g : graph loc) (G : Gmon) x i v :
  i ≠ x → of_graph g ((x [↦] v) ⋅ G) !! i = (of_graph g G) !! i.
Proof.
  intros H. rewrite /of_graph /of_graph_elem ?map_lookup_imap ?lookup_omap; simpl.
  rewrite mark_update_lookup_ne_base //=.
Qed.

Section graph.
  Context `{heapGS Σ, graphG Σ}.

  Lemma own_graph_valid q G : own_graph q G ⊢ ✓ G.
  Proof.
    iIntros "H". unfold own_graph.
    by iDestruct (own_valid with "H") as %[_ ?]%auth_frag_valid.
  Qed.

  Lemma auth_own_graph_valid q G : own graph_name (● Some (q, G))  ⊢ ✓ G.
  Proof.
    iIntros "H". unfold own_graph.
    iDestruct (own_valid with "H") as %VAL.
    move : VAL => /auth_auth_valid [_ ?] //.
  Qed.

  Lemma whole_frac (G G' : Gmon):
    own graph_name (● Some (1%Qp, G)) ∗ own_graph 1 G' ⊢ ⌜G = G'⌝.
  Proof.
    iIntros "[H1 H2]". rewrite /own_graph.
    iCombine "H1" "H2" as "H".
    iDestruct (own_valid with "H") as %[H1 H2]%auth_both_valid_discrete.
    iPureIntro.
    apply option_included in H1; destruct H1 as [H1|H1]; [inversion H1|].
    destruct H1 as (u1 & u2 & Hu1 & Hu2 & H3);
      inversion Hu1; inversion Hu2; subst.
    destruct H3 as [[_ H31%leibniz_equiv]|H32]; auto.
    inversion H32 as [[q x] H4].
    inversion H4 as [H41 H42]; simpl in *.
    assert (✓ (1 ⋅ q)%Qp) by (rewrite -H41; done).
    exfalso; eapply exclusive_l; eauto; typeclasses eauto.
  Qed.

  Lemma graph_divide q G G' :
    own_graph q (G ⋅ G') ⊣⊢ own_graph (q / 2) G ∗ own_graph (q / 2) G'.
  Proof.
    replace q with ((q / 2) + (q / 2))%Qp at 1 by (by rewrite Qp.div_2).
      by rewrite /own_graph -own_op.
  Qed.

  Lemma mark_graph {E} (G : Gmon) q x w : G !! x = None →
    own graph_name (● Some (1%Qp, G)) ∗ own_graph q ∅
    ={E}=∗
    own graph_name (● Some (1%Qp, {[x := Excl w]} ⋅ G)) ∗ own_graph q (x [↦] w).
  Proof.
    iIntros (Hx) "H". rewrite -?own_op.
    iMod (own_update with "H") as "H'"; eauto.
    apply auth_update, option_local_update, prod_local_update;
      first done; simpl.
    rewrite -{2}[(x [↦] w)]right_id.
    apply op_local_update_discrete; auto.
    rewrite -insert_singleton_op; trivial. apply insert_valid; done.
  Qed.

  Lemma update_graph {E} (G : Gmon) q x w m :
    G !! x = None →
    own graph_name (● Some (1%Qp, {[x := Excl m]} ⋅ G))
       ∗ own_graph q (x [↦] m)
      ⊢ |={E}=> own graph_name (● Some (1%Qp, {[x := Excl w]} ⋅ G))
                  ∗ own_graph q (x [↦] w).
  Proof.
    iIntros (Hx) "H". rewrite -?own_op.
    iMod (own_update with "H") as "H'"; eauto.
    apply auth_update, option_local_update, prod_local_update;
      first done; simpl.
    rewrite -!insert_singleton_op; trivial.
    replace (<[x:=Excl w]> G) with (<[x:=Excl w]> (<[x:=Excl m]> G))
      by (by rewrite insert_insert).
    eapply singleton_local_update; first (by rewrite lookup_insert);
    apply exclusive_local_update; done.
  Qed.

  Lemma graph_pointsto_marked (G : Gmon) q x w :
    own graph_name (● Some (1%Qp, G)) ∗ own_graph q (x [↦] w)
      ⊢ ⌜G = {[x := Excl w]} ⋅ (delete x G)⌝.
  Proof.
    rewrite /own_graph -?own_op. iIntros "H".
    iDestruct (own_valid with "H") as %[H1 H2]%auth_both_valid_discrete.
    iPureIntro.
    apply option_included in H1; destruct H1 as [H1|H1]; [inversion H1|].
    destruct H1 as (u1 & u2 & Hu1 & Hu2 & H1);
      inversion Hu1; inversion Hu2; subst.
    destruct H1 as [[_ H11%leibniz_equiv]|H12]; simpl in *.
    + by rewrite -H11 delete_singleton right_id_L.
    + apply prod_included in H12; destruct H12 as [_ H12]; simpl in *.
      rewrite -insert_singleton_op ?insert_delete_insert; last by rewrite lookup_delete.
      apply: map_eq => i. apply leibniz_equiv, equiv_dist => n.
      destruct (decide (x = i)); subst;
        rewrite ?lookup_insert ?lookup_insert_ne //.
      apply singleton_included_l in H12. destruct H12 as [y [H31 H32]].
      rewrite H31 (Some_included_exclusive _ _ H32); try done.
      destruct H2 as [H21 H22]; simpl in H22.
      specialize (H22 i); revert H22; rewrite H31; done.
  Qed.

  Lemma graph_open (g :graph loc) (markings : gmap loc loc) (G : Gmon) x
  : x ∈ dom g →
    own graph_name (● Some (1%Qp, G)) ∗ heap_owns (of_graph g G) markings ⊢
    own graph_name (● Some (1%Qp, G))
    ∗ heap_owns (delete x (of_graph g G)) markings
    ∗ (∃ u : bool * (option loc * option loc), ⌜of_graph g G !! x = Some u⌝
         ∗ ∃ (m : loc), ⌜markings !! x = Some m⌝ ∗ x ↦ (#m, children_to_val (u.2))
           ∗ m ↦ #(u.1)).
  Proof.
    iIntros (Hx) "(Hg & Ha)".
    assert (Hid : x ∈ dom (of_graph g G)) by (by rewrite of_graph_dom).
    revert Hid; rewrite elem_of_dom /is_Some. intros [y Hy].
    rewrite /heap_owns -{1}(insert_id _ _ _ Hy) -insert_delete_insert.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
    iDestruct "Ha" as "[H $]". iFrame "Hg". iExists _; eauto.
  Qed.

  Lemma graph_close g markings G x :
    heap_owns (delete x (of_graph g G)) markings
    ∗ (∃ u : bool * (option loc * option loc), ⌜of_graph g G !! x = Some u⌝
        ∗ ∃ (m : loc), ⌜markings !! x = Some m⌝ ∗ x ↦ (#m, children_to_val (u.2))
            ∗ m ↦ #(u.1))
    ⊢ heap_owns (of_graph g G) markings.
  Proof.
    iIntros "[Ha Hl]". iDestruct "Hl" as (u) "[Hu Hl]". iDestruct "Hu" as %Hu.
    rewrite /heap_owns -{2}(insert_id _ _ _ Hu) -insert_delete_insert.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto]. by iFrame "Ha".
  Qed.

  Lemma marked_is_marked_in_auth (mr : gset loc) l :
    own graph_marking_name (● mr) ∗ is_marked l ⊢ ⌜l ∈ mr⌝.
  Proof.
    iIntros "H". unfold is_marked. rewrite -own_op.
    iDestruct (own_valid with "H") as %Hvl.
    move : Hvl => /auth_both_valid_discrete [[z Hvl'] _].
    iPureIntro.
    rewrite Hvl' /= !gset_op !elem_of_union elem_of_singleton; tauto.
  Qed.

  Lemma marked_is_marked_in_auth_sepS (mr : gset loc) m :
    own graph_marking_name (● mr) ∗ ([∗ set] l ∈ m, is_marked l) ⊢ ⌜m ⊆ mr⌝.
  Proof.
    iIntros "[Hmr Hm]". rewrite big_sepS_forall bi.pure_forall.
    iIntros (x). rewrite bi.pure_impl. iIntros (Hx).
    iApply marked_is_marked_in_auth.
    iFrame. by iApply "Hm".
  Qed.

End graph.

(* Graph properties *)

Lemma delete_marked g G x w :
  delete x (of_graph g G) = delete x (of_graph g ((x [↦] w) ⋅ G)).
Proof.
  apply: map_eq => i. destruct (decide (i = x)).
  - subst; by rewrite ?lookup_delete.
  - rewrite ?lookup_delete_ne //= /of_graph /of_graph_elem ?map_lookup_imap
      ?lookup_omap; case _ : (g !! i) => [v|] //=.
    by rewrite lookup_op lookup_singleton_ne //= left_id_L.
Qed.

Lemma in_dom_conv (G G' : Gmon) x : ✓ (G ⋅ G') → x ∈ dom (Gmon_graph G)
  → (Gmon_graph (G ⋅ G')) !! x = (Gmon_graph G) !! x.
Proof.
  intros HGG. specialize (HGG x). revert HGG.
  rewrite /get_left /Gmon_graph elem_of_dom /is_Some ?lookup_omap lookup_op.
  case _ : (G !! x) => [[]|]; case _ : (G' !! x) => [[]|]; do 2 inversion 1;
    simpl in *; auto; congruence.
Qed.
Lemma in_dom_conv' (G G' : Gmon) x: ✓(G ⋅ G') → x ∈ dom (Gmon_graph G')
  → (Gmon_graph (G ⋅ G')) !! x = (Gmon_graph G') !! x.
Proof. rewrite comm; apply in_dom_conv. Qed.
Lemma get_left_conv (G G' : Gmon) x xl : ✓ (G ⋅ G') →
  x ∈ dom (Gmon_graph G) → get_left (Gmon_graph (G ⋅ G')) x = Some xl
  ↔ get_left (Gmon_graph G) x = Some xl.
Proof. intros. rewrite /get_left in_dom_conv; auto. Qed.
Lemma get_left_conv' (G G' : Gmon) x xl : ✓ (G ⋅ G') →
  x ∈ dom (Gmon_graph G') → get_left (Gmon_graph (G ⋅ G')) x = Some xl
  ↔ get_left (Gmon_graph G') x = Some xl.
Proof. rewrite comm; apply get_left_conv. Qed.
Lemma get_right_conv (G G' : Gmon) x xl : ✓ (G ⋅ G') →
  x ∈ dom (Gmon_graph G) → get_right (Gmon_graph (G ⋅ G')) x = Some xl
  ↔ get_right (Gmon_graph G) x = Some xl.
Proof. intros. rewrite /get_right in_dom_conv; auto. Qed.
Lemma get_right_conv' (G G' : Gmon) x xl : ✓ (G ⋅ G') →
  x ∈ dom (Gmon_graph G') → get_right (Gmon_graph (G ⋅ G')) x = Some xl
  ↔ get_right (Gmon_graph G') x = Some xl.
Proof. rewrite comm; apply get_right_conv. Qed.

Lemma in_op_dom (G G' : Gmon) y : ✓(G ⋅ G') →
  y ∈ dom (Gmon_graph G) → y ∈ dom (Gmon_graph (G ⋅ G')).
Proof. refine (λ H x, _ x); rewrite ?elem_of_dom ?in_dom_conv ; eauto. Qed.
Lemma in_op_dom' (G G' : Gmon) y : ✓(G ⋅ G') →
  y ∈ dom (Gmon_graph G') → y ∈ dom (Gmon_graph (G ⋅ G')).
Proof. rewrite comm; apply in_op_dom. Qed.

Local Hint Resolve cmra_valid_op_l cmra_valid_op_r in_op_dom in_op_dom' : core.

Lemma in_op_dom_alt (G G' : Gmon) y : ✓(G ⋅ G') →
  y ∈ dom G → y ∈ dom (G ⋅ G').
Proof. intros HGG; rewrite -?Gmon_graph_dom; eauto. Qed.
Lemma in_op_dom_alt' (G G' : Gmon) y : ✓(G ⋅ G') →
  y ∈ dom G' → y ∈ dom (G ⋅ G').
Proof. intros HGG; rewrite -?Gmon_graph_dom; eauto. Qed.

Local Hint Resolve in_op_dom_alt in_op_dom_alt' : core.
Local Hint Extern 1 => eapply get_left_conv + eapply get_left_conv' +
  eapply get_right_conv + eapply get_right_conv' : core.

Local Hint Extern 1 (_ ∈ dom (Gmon_graph _)) =>
  erewrite Gmon_graph_dom : core.

Local Hint Resolve path_start path_end : core.

Lemma path_conv (G G' : Gmon) x y p :
  ✓ (G ⋅ G') → maximal (Gmon_graph G) → x ∈ dom G →
  valid_path (Gmon_graph (G ⋅ G')) x y p → valid_path (Gmon_graph G) x y p.
Proof.
  intros Hv Hm. rewrite -Gmon_graph_dom //=; eauto. revert x y.
  induction p as [|[] p IHp]; inversion 2; subst; econstructor; eauto;
    try eapply IHp; try eapply Hm; eauto.
Qed.
Lemma path_conv_back (G G' : Gmon) x y p :
  ✓ (G ⋅ G') → x ∈ dom G →
  valid_path (Gmon_graph G) x y p → valid_path (Gmon_graph (G ⋅ G')) x y p.
Proof.
  intros Hv. rewrite -Gmon_graph_dom //=; eauto. revert x y.
  induction p as [|[] p]; inversion 2; subst; econstructor; eauto.
Qed.
Lemma path_conv' (G G' : Gmon) x y p :
  ✓ (G ⋅ G') → maximal (Gmon_graph G') → x ∈ dom G' →
  valid_path (Gmon_graph (G ⋅ G')) x y p → valid_path (Gmon_graph G') x y p.
Proof. rewrite comm; eapply path_conv. Qed.
Lemma path_conv_back' (G G' : Gmon) x y p :
  ✓ (G ⋅ G') → x ∈ dom G' →
  valid_path (Gmon_graph G') x y p → valid_path (Gmon_graph (G ⋅ G')) x y p.
Proof. rewrite comm; apply path_conv_back. Qed.

Local Ltac in_dom_Gmon_graph :=
  rewrite Gmon_graph_dom //= ?dom_op ?elem_of_union ?dom_singleton
      ?elem_of_singleton.

Lemma get_left_singleton x vl vr :
  get_left (Gmon_graph (x [↦] (vl, vr))) x = vl.
Proof. rewrite /get_left /Gmon_graph lookup_omap lookup_singleton; done. Qed.
Lemma get_right_singleton x vl vr :
  get_right (Gmon_graph (x [↦] (vl, vr))) x = vr.
Proof. rewrite /get_right /Gmon_graph lookup_omap lookup_singleton; done. Qed.

Lemma graph_in_dom_op (G G' : Gmon) x :
  ✓ (G ⋅ G') → x ∈ dom G → x ∉ dom G'.
Proof.
  intros HGG. specialize (HGG x). revert HGG. rewrite ?elem_of_dom lookup_op.
  case _ : (G !! x) => [[]|]; case _ : (G' !! x) => [[]|]; inversion 1;
  do 2 (intros [? Heq]; inversion Heq; clear Heq).
Qed.
Lemma graph_in_dom_op' (G G' : Gmon) x :
  ✓ (G ⋅ G') → x ∈ dom G' → x ∉ dom G.
Proof. rewrite comm; apply graph_in_dom_op. Qed.
Lemma graph_op_path (G G' : Gmon) x z p :
  ✓ (G ⋅ G') → x ∈ dom G → valid_path (Gmon_graph G') z x p → False.
Proof.
  intros ?? Hp%path_end; rewrite Gmon_graph_dom in Hp; eauto.
  eapply graph_in_dom_op; eauto.
Qed.
Lemma graph_op_path' (G G' : Gmon) x z p :
  ✓ (G ⋅ G') → x ∈ dom G' → valid_path (Gmon_graph G) z x p → False.
Proof. rewrite comm; apply graph_op_path. Qed.

Lemma in_dom_singleton (x : loc) (w : chlO) :
  x ∈ dom (x [↦] w : gmap loc _).
Proof. by rewrite dom_singleton elem_of_singleton. Qed.


Local Hint Resolve graph_op_path graph_op_path' in_dom_singleton : core.

Lemma maximal_op (G G' : Gmon) : ✓ (G ⋅ G') → maximal (Gmon_graph G)
  → maximal (Gmon_graph G') → maximal (Gmon_graph (G ⋅ G')).
Proof.
  intros Hvl [_ HG] [_ HG']. split; trivial => x v.
  rewrite Gmon_graph_dom ?dom_op ?elem_of_union -?Gmon_graph_dom; eauto.
  intros [Hxl|Hxr].
  - erewrite get_left_conv, get_right_conv; eauto.
  - erewrite get_left_conv', get_right_conv'; eauto.
Qed.

Lemma maximal_op_singleton (G : Gmon) x vl vr :
  ✓ ((x [↦] (vl, vr)) ⋅ G) → maximal(Gmon_graph G) →
  match vl with | Some xl => xl ∈ dom G | None => True end →
  match vr with | Some xr => xr ∈ dom G | None => True end →
  maximal (Gmon_graph ((x [↦] (vl, vr)) ⋅ G)).
Proof.
  intros HGG [_ Hmx] Hvl Hvr; split; trivial => z v. in_dom_Gmon_graph.
  intros [Hv|Hv]; subst.
  - erewrite get_left_conv, get_right_conv, get_left_singleton,
          get_right_singleton; eauto.
    destruct vl as [xl|]; destruct vr as [xr|]; intros [Hl|Hr];
      try inversion Hl; try inversion Hr; subst; eauto.
  - erewrite get_left_conv', get_right_conv', <- Gmon_graph_dom; eauto.
Qed.

Local Hint Resolve maximal_op_singleton maximal_op get_left_singleton
  get_right_singleton : core.

Lemma maximally_marked_tree_both (G G' : Gmon) x xl xr :
  ✓ ((x [↦] (Some xl, Some xr)) ⋅ (G ⋅ G')) →
  xl ∈ dom G → tree (Gmon_graph G) xl → maximal (Gmon_graph G) →
  xr ∈ dom G' → tree (Gmon_graph G') xr → maximal (Gmon_graph G') →
  tree (Gmon_graph ((x [↦] (Some xl, Some xr)) ⋅ (G ⋅ G'))) x ∧
  maximal (Gmon_graph ((x [↦] (Some xl, Some xr)) ⋅ (G ⋅ G'))).
Proof.
  intros Hvl Hxl tl ml Hxr tr mr; split.
  - intros l. in_dom_Gmon_graph. intros [?|[HlG|HlG']]; first subst.
    + exists []; split.
      { constructor 1; trivial. in_dom_Gmon_graph; auto. }
      { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso. apply get_left_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_left_singleton in Hl; inversion Hl; subst.
          apply path_conv' in Hpv; eauto.
        - exfalso. apply get_right_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_right_singleton in Hl; inversion Hl; subst.
          apply path_conv' in Hpv; eauto. }
   + edestruct tl as [q [qv Hq]]; eauto.
     exists (true :: q). split; [econstructor; eauto|].
     { eapply path_conv_back'; eauto; eapply path_conv_back; eauto. }
     { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso; eapply path_conv_back in qv; eauto.
        - apply get_left_conv in Hl; eauto.
          rewrite get_left_singleton in Hl. inversion Hl; subst.
          apply path_conv', path_conv in Hpv; eauto. erewrite Hq; eauto.
        - exfalso. apply get_right_conv in Hl; eauto.
          rewrite get_right_singleton in Hl; inversion Hl; subst.
          do 2 apply path_conv' in Hpv; eauto. }
  + edestruct tr as [q [qv Hq]]; eauto.
     exists (false :: q). split; [econstructor; eauto|].
     { eapply path_conv_back'; eauto; eapply path_conv_back'; eauto. }
     { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso; eapply path_conv_back' in qv; eauto.
        - exfalso. apply get_left_conv in Hl; eauto.
          rewrite get_left_singleton in Hl; inversion Hl; subst.
          apply path_conv', path_conv in Hpv; eauto.
        - apply get_right_conv in Hl; eauto.
          rewrite get_right_singleton in Hl. inversion Hl; subst.
          apply path_conv', path_conv' in Hpv; eauto. erewrite Hq; eauto. }
  - apply maximal_op_singleton; eauto.
Qed.

Lemma maximally_marked_tree_left (G : Gmon) x xl :
  ✓ ((x [↦] (Some xl, None)) ⋅ G) →
  xl ∈ dom G → tree (Gmon_graph G) xl → maximal (Gmon_graph G) →
  tree (Gmon_graph ((x [↦] (Some xl, None)) ⋅ G)) x ∧
  maximal (Gmon_graph ((x [↦] (Some xl, None)) ⋅ G)).
Proof.
  intros Hvl Hxl tl ml; split.
  - intros l. in_dom_Gmon_graph. intros [?|HlG]; first subst.
    + exists []; split.
      { constructor 1; trivial. in_dom_Gmon_graph; auto. }
      { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso. apply get_left_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_left_singleton in Hl; inversion Hl; subst.
          apply path_conv' in Hpv; eauto.
        - exfalso. apply get_right_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_right_singleton in Hl; inversion Hl. }
   + edestruct tl as [q [qv Hq]]; eauto.
     exists (true :: q). split; [econstructor; eauto|].
     { eapply path_conv_back'; eauto; eapply path_conv_back; eauto. }
     { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso; eauto.
        - apply get_left_conv in Hl; eauto.
          rewrite get_left_singleton in Hl. inversion Hl; subst.
          apply path_conv' in Hpv; eauto. erewrite Hq; eauto.
        - exfalso. apply get_right_conv in Hl; eauto.
          rewrite get_right_singleton in Hl; inversion Hl. }
 - apply maximal_op_singleton; eauto.
Qed.

Lemma maximally_marked_tree_right (G : Gmon) x xr :
  ✓ ((x [↦] (None, Some xr)) ⋅ G) →
  xr ∈ dom G → tree (Gmon_graph G) xr → maximal (Gmon_graph G) →
  tree (Gmon_graph ((x [↦] (None, Some xr)) ⋅ G)) x ∧
  maximal (Gmon_graph ((x [↦] (None, Some xr)) ⋅ G)).
Proof.
  intros Hvl Hxl tl ml; split.
  - intros l. in_dom_Gmon_graph. intros [?|HlG]; first subst.
    + exists []; split.
      { constructor 1; trivial. in_dom_Gmon_graph; auto. }
      { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso. apply get_left_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_left_singleton in Hl; inversion Hl.
        - exfalso. apply get_right_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_right_singleton in Hl; inversion Hl; subst.
          apply path_conv' in Hpv; eauto. }
   + edestruct tl as [q [qv Hq]]; eauto.
     exists (false :: q). split; [econstructor; eauto|].
     { eapply path_conv_back'; eauto; eapply path_conv_back; eauto. }
     { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso; eauto.
        - exfalso. apply get_left_conv in Hl; eauto.
          rewrite get_left_singleton in Hl; inversion Hl.
        - apply get_right_conv in Hl; eauto.
          rewrite get_right_singleton in Hl. inversion Hl; subst.
          apply path_conv' in Hpv; eauto. erewrite Hq; eauto. }
 - apply maximal_op_singleton; eauto.
Qed.

Lemma maximally_marked_tree_none (x : loc) :
  ✓ ((x [↦] (None, None)) : Gmon) →
  tree (Gmon_graph (x [↦] (None, None))) x ∧
  maximal (Gmon_graph (x [↦] (None, None))).
Proof.
  intros Hvl; split.
  - intros l. in_dom_Gmon_graph. intros ?; subst.
    + exists []; split.
      { constructor 1; trivial. in_dom_Gmon_graph; auto. }
      { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - rewrite get_left_singleton in Hl; inversion Hl.
        - rewrite get_right_singleton in Hl; inversion Hl. }
 - split; trivial. intros z v. in_dom_Gmon_graph. intros ? [Hl|Hl]; subst.
    + rewrite get_left_singleton in Hl; inversion Hl.
    + rewrite get_right_singleton in Hl; inversion Hl.
Qed.

Lemma update_valid (G : Gmon) x v w : ✓ ((x [↦] v) ⋅ G) → ✓ ((x [↦] w) ⋅ G).
Proof.
  intros Hvl i; specialize (Hvl i); revert Hvl.
  rewrite ?lookup_op. destruct (decide (i = x)).
  - subst; rewrite ?lookup_singleton; case _ : (G !! x); done.
  - rewrite ?lookup_singleton_ne //=.
Qed.

Lemma of_graph_unmarked (g : graph loc) (G : Gmon) x v :
  of_graph g G !! x = Some (false, v) → g !! x = Some v.
Proof.
  rewrite map_lookup_imap /of_graph_elem lookup_omap.
  case _ : (g !! x); case _ : (G !! x) => [[]|]; by inversion 1.
Qed.
Lemma get_lr_disj (G G' : Gmon) i : ✓ (G ⋅ G') →
  (get_left (Gmon_graph (G ⋅ G')) i = get_left (Gmon_graph G) i ∧
   get_right (Gmon_graph (G ⋅ G')) i = get_right (Gmon_graph G) i ∧
   get_left (Gmon_graph G') i = None ∧
   get_right (Gmon_graph G') i = None) ∨
  (get_left (Gmon_graph (G ⋅ G')) i = get_left (Gmon_graph G') i ∧
   get_right (Gmon_graph (G ⋅ G')) i = get_right (Gmon_graph G') i ∧
   get_left (Gmon_graph G) i = None ∧
   get_right (Gmon_graph G) i = None).
Proof.
  intros Hvl. specialize (Hvl i). revert Hvl.
  rewrite /get_left /get_right /Gmon_graph ?lookup_omap ?lookup_op.
  case _ : (G !! i) => [[]|]; case _ : (G' !! i) => [[]|]; inversion 1;
    simpl; auto.
Qed.
Lemma mark_update_strict_subgraph (g : graph loc) (G G' : Gmon) : ✓ (G ⋅ G') →
  strict_subgraph g (Gmon_graph G) ∧ strict_subgraph g (Gmon_graph G') ↔
  strict_subgraph g (Gmon_graph (G ⋅ G')).
Proof.
  intros Hvl; split.
  - intros [HG HG'] i.
  destruct (get_lr_disj G G' i) as [(-> & -> & _ & _)|(-> & -> & _ & _)]; eauto.
  - intros HGG; split => i.
    + destruct (get_lr_disj G G' i) as [(<- & <- & _ & _)|(_ & _ & -> & ->)];
       eauto using strict_sub_children_None.
    + destruct (get_lr_disj G G' i) as [(_ & _ & -> & ->)|(<- & <- & _ & _)];
       eauto using strict_sub_children_None.
Qed.
Lemma strinct_subgraph_singleton (g : graph loc) x v :
  x ∈ dom g → (∀ w, g !! x = Some w → strict_sub_children w v)
  ↔ strict_subgraph g (Gmon_graph (x [↦] v)).
Proof.
  rewrite elem_of_dom; intros [u Hu]; split.
  - move => /(_ _ Hu) Hgw i.
    rewrite /get_left /get_right /Gmon_graph lookup_omap.
    destruct (decide (i = x)); subst.
    + by rewrite Hu lookup_singleton; simpl.
    + rewrite lookup_singleton_ne; auto. by case _ : (g !! i) => [[[?|] [?|]]|].
  - intros Hg w Hw; specialize (Hg x). destruct v as [v1 v2]; simpl. revert Hg.
    rewrite Hu in Hw; inversion Hw; subst.
    by rewrite get_left_singleton get_right_singleton /get_left /get_right Hu.
Qed.
Lemma mark_strict_subgraph (g : graph loc) (G : Gmon) x v :
  ✓ ((x [↦] v) ⋅ G) → x ∈ dom g →
  of_graph g G !! x = Some (false, v) → strict_subgraph g (Gmon_graph G) →
  strict_subgraph g (Gmon_graph ((x [↦] v) ⋅ G)).
Proof.
  intros Hvl Hdx Hx Hsg. apply mark_update_strict_subgraph; try split; eauto.
  eapply strinct_subgraph_singleton; erewrite ?of_graph_unmarked; eauto.
  inversion 1; auto using strict_sub_children_refl.
Qed.
Lemma update_strict_subgraph (g : graph loc) (G : Gmon) x v w :
  ✓ ((x [↦] v) ⋅ G) → x ∈ dom g →
  strict_subgraph g (Gmon_graph ((x [↦] w) ⋅ G)) →
  strict_sub_children w v →
  strict_subgraph g (Gmon_graph ((x [↦] v) ⋅ G)).
Proof.
  intros Hvl Hdx Hx Hsc1 Hsc2.
  apply mark_update_strict_subgraph in Hx; eauto using update_valid.
  destruct Hx as [Hx1 Hx2].
  apply mark_update_strict_subgraph; try split; try tauto.
  pose proof (proj1 (elem_of_dom _ _) Hdx) as [u Hu].
  eapply strinct_subgraph_singleton in Hx1; eauto.
  apply strinct_subgraph_singleton; trivial.
  intros u' Hu'; rewrite Hu in Hu'; inversion Hu'; subst.
  intuition eauto using strict_sub_children_trans.
Qed.
