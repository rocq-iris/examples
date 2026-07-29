From iris.algebra Require Import excl auth gmap agree.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation par.
From iris_examples.logatom.snapshot Require Import spec.

(** Specifying snapshots with histories
    Inspired by atomic pair snapshot data structure from Sergey et al. (ESOP 2015) *)


(*
     new_snapshot v :=
       ref (ref (v, 0))
 *)
Definition new_snapshot : val :=
  λ: "v",
    ref (ref ("v", #0)).

(*
    write xp x :=
      let xp1 = !xp in
      let v   = (!xp1).2
      let xp2 = ref (x, v + 1)
      // This is where we need the nested references: the CAS compares the old
      // inner reference with the new one, because it cannot atomically compared
      // a pair of values.
      if CAS xp xp1 xp2
        then ()
        else writeX (xp, yp) x
 *)
Definition write : val :=
  rec: "write" "xp" "x" :=
    let: "xp1"  := !"xp"                  in
    let: "v"    := Snd (!"xp1")           in
    let: "xp2"  := ref ("x", "v" + #1)    in
    if: CAS "xp" "xp1" "xp2"
    then #()
    else "write" "xp" "x".

(*
    read xp :=
      (!!xp).1
 *)
Definition read : val :=
  λ: "xp",
    Fst !(!"xp").

(*
    read_with xp l :=
      let (x, v)  = !!xp in
      let y       = !l in
      let (_, v') = !!xp in
      if v = v'
        then (x, y)
        else read_with l
 *)
Definition read_with_proph : val :=
  rec: "read_with" "xp" "l" :=
    let: "proph"  := NewProph in
    let: "x"  := ! !"xp" in
    let: "y"  := !"l" in
    let: "x'" := ! !"xp" in
    let: "v_eq"   := Snd "x" = Snd "x'" in
    resolve_proph: "proph" to: "v_eq" ;;
    if: "v_eq"
    then (Fst "x", "y")
    else  "read_with" "xp" "l".


(** The CMRA & functor we need. *)

Definition timestampUR := gmapUR Z $ agreeR valO.

Class atomic_snapshotG Σ := AtomicSnapshotG {
                                atomic_snapshot_stateG :: inG Σ $ authR $ optionUR $ exclR $ valO;
                                atomic_snapshot_timestampG :: inG Σ $ authR $ timestampUR
}.
Definition atomic_snapshotΣ : gFunctors :=
  #[GFunctor (authR $ optionUR $ exclR $ valO); GFunctor (authR timestampUR)].

Global Instance subG_atomic_snapshotΣ {Σ} : subG atomic_snapshotΣ Σ → atomic_snapshotG Σ.
Proof. solve_inG. Qed.

Section atomic_snapshot.

  Context {Σ} `{!heapGS Σ, !atomic_snapshotG Σ}.

  Variable N: namespace.

  Definition gmap_to_UR T : timestampUR := to_agree <$> T.

  Definition snapshot_inv γ1 γ2 l1 : iProp Σ :=
    (∃ (l1':loc) (T : gmap Z val) x (t : Z),
      (* we add the q to make the l1' map fractional. that way,
         we can take a fraction of the l1' map out of the invariant
         and do a case analysis on whether the pointer is the same
         throughout invariant openings *)
      l1 ↦ #l1' ∗ l1' ↦□ (x, #t) ∗
         own γ1 (● Excl' x) ∗ own γ2 (● gmap_to_UR T) ∗
         ⌜T !! t = Some x⌝ ∗
         ⌜∀ (t' : Z), t' ∈ dom T → (t' ≤ t)%Z⌝)%I.

  Definition is_snapshot (γs: gname * gname) (p : val) :=
    (∃ (l1 : loc), ⌜p = #l1%V⌝ ∗ inv N (snapshot_inv γs.1 γs.2 l1))%I.

  Global Instance is_snapshot_persistent γs p : Persistent (is_snapshot γs p) := _.

  Definition snapshot_content (γs : gname * gname) (a : val) :=
    (own γs.1 (◯ Excl' a))%I.

  Global Instance snapshot_content_timeless γs a : Timeless (snapshot_content γs a) := _.

  Lemma snapshot_content_exclusive γs a1 a2 :
    snapshot_content γs a1 -∗ snapshot_content γs a2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iCombine "H1 H2" gives %[]%auth_frag_op_valid_1.
  Qed.

  Definition new_timestamp t v : gmap Z val := {[ t := v ]}.

  Lemma new_snapshot_spec (v : val) :
      {{{ True }}}
        new_snapshot v
      {{{ γs p, RET p; is_snapshot γs p ∗ snapshot_content γs v }}}.
  Proof.
    iIntros (Φ _) "Hx". rewrite /new_snapshot. wp_lam.
    repeat (wp_proj; wp_let).
    wp_alloc lx' as "Hlx'".
    iMod (pointsto_persist with "Hlx'") as "Hlx'".
    wp_alloc lx as "Hlx".
    set (Excl' v) as p.
    iMod (own_alloc (● p ⋅ ◯ p)) as (γ1) "[Hx⚫ Hx◯]". {
      rewrite /p. apply auth_both_valid_discrete. split; done.
    }
    set (new_timestamp 0 v) as t.
    iMod (own_alloc (● gmap_to_UR t ⋅ ◯ gmap_to_UR t)) as (γ2) "[Ht⚫ Ht◯]". {
      rewrite /t /new_timestamp. apply auth_both_valid_discrete.
      split; first done. rewrite /gmap_to_UR map_fmap_singleton. apply singleton_valid. done.
    }
    iApply ("Hx" $! (γ1, γ2)).
    iMod (inv_alloc N _ (snapshot_inv γ1 γ2 _) with "[-Hx◯ Ht◯]") as "#Hinv". {
      iNext. rewrite /snapshot_inv. iExists _, _, _, 0. iFrame.
      iPureIntro. split; first done. intros ?. subst t. rewrite /new_timestamp dom_singleton.
      rewrite elem_of_singleton. lia.
    }
    iModIntro. rewrite /is_snapshot /snapshot_content. iFrame. iExists _.
    iSplitL; first done. done.
  Qed.

 Lemma excl_update γ n' n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) ==∗
      own γ (● (Excl' n')) ∗ own γ (◯ (Excl' n')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' n' ⋅ ◯ Excl' n') with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  Lemma excl_sync γ n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) -∗ ⌜m = n⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    iCombine "Hγ● Hγ◯" gives
        %[H%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    done.
  Qed.

  Lemma timestamp_dupl γ T:
    own γ (● T) ==∗ own γ (● T) ∗ own γ (◯ T).
  Proof.
    iIntros "Ht". iApply own_op. iApply (own_update with "Ht").
    apply auth_update_alloc. apply local_update_unital_discrete => f Hv. rewrite left_id => <-.
    split; first done. apply core_id_dup. apply _.
  Qed.

  Lemma timestamp_update γ (T : gmap Z val) (t : Z) x :
    T !! t = None →
    own γ (● gmap_to_UR T) ==∗ own γ (● gmap_to_UR (<[ t := x ]> T)).
  Proof.
    iIntros (HT) "Ht".
    set (<[ t := x ]> T) as T'.
    iDestruct (own_update _ _ (● gmap_to_UR T' ⋅ ◯ gmap_to_UR {[ t := x ]}) with "Ht") as "Ht". {
      apply auth_update_alloc. rewrite /T' /gmap_to_UR map_fmap_singleton. rewrite fmap_insert.
      apply alloc_local_update; last done. rewrite lookup_fmap HT. done.
    }
    iMod (own_op with "Ht") as "[Ht● Ht◯]". iModIntro. iFrame.
  Qed.

  Lemma timestamp_sub γ (T1 T2 : gmap Z val):
    own γ (● gmap_to_UR T1) ∗ own γ (◯ gmap_to_UR T2) -∗
    ⌜∀ t x, T2 !! t = Some x → T1 !! t = Some x⌝.
  Proof.
    iIntros "[Hγ⚫ Hγ◯]".
    iCombine "Hγ⚫ Hγ◯" gives
        %[H Hv]%auth_both_valid_discrete. iPureIntro. intros t x HT2.
    pose proof (iffLR (lookup_included (gmap_to_UR T2) (gmap_to_UR T1)) H t) as Ht.
    rewrite !lookup_fmap HT2 /= in Ht.
    destruct (is_Some_included _ _ Ht) as [? [t2 [Ht2 ->]]%fmap_Some_1]; first by eauto.
    revert Ht.
    rewrite Ht2 Some_included_total to_agree_included. fold_leibniz.
    by intros ->.
  Qed.

  Lemma write_spec γ (x2: val) p :
      is_snapshot γ p  -∗
      <<{ ∀∀ x : val, snapshot_content γ x }>>
        write p x2 @ ↑N
      <<{ snapshot_content γ x2 | RET #() }>>.
  Proof.
    iIntros "Hx". iIntros (Φ) "AU". iLöb as "IH".
    iDestruct "Hx" as (l1 ->) "#Hinv". wp_pures. wp_lam. wp_pures.
    (* first read *)
    (* open invariant *)
    wp_bind (!_)%E. iInv N as (l1' T x v') "[Hl1 [#Hl1' [Hx⚫ Htime]]]".
      wp_load.
      iModIntro. iSplitR "AU".
      (* close invariant *)
      { iNext. rewrite /snapshot_inv. eauto 10 with iFrame. }
    wp_let. wp_bind (!_)%E. clear T.
    wp_load. wp_proj. wp_let. wp_op. wp_alloc l1'new as "Hl1'new".
    wp_let.
    (* CAS *)
    wp_bind (CmpXchg _ _ _)%E.
    (* open invariant *)
    iInv N as (l1'' T x' v'') ">[Hl1 [#Hl1'' [Hx⚫ [Ht● Ht]]]]".
    iDestruct "Ht" as %[Ht Hvt].
    destruct (decide (l1'' = l1')) as [-> | Hn].
    - wp_cmpxchg_suc.
      iMod (pointsto_persist with "Hl1'new") as "Hl1'new".
      iDestruct (pointsto_agree with "Hl1' Hl1''") as %[= -> ->].
      (* open AU *)
      iMod "AU" as (xv) "[Hx [_ Hclose]]".
        (* update snapshot ghost state to (x2, y') *)
        iDestruct (excl_sync with "Hx⚫ Hx") as %[= ->].
        iMod (excl_update _ x2 with "Hx⚫ Hx") as "[Hx⚫ Hx◯]".
        (* close AU *)
        iMod ("Hclose" with "Hx◯") as "HΦ".
      (* update timestamp *)
      iMod (timestamp_update _ T (v'' + 1)%Z x2 with "[Ht●]") as "Ht".
      { eapply (not_elem_of_dom T). intros Hd. specialize (Hvt _ Hd). lia. }
      { done. }
      (* close invariant *)
      iModIntro. iSplitR "HΦ".
      + iNext. rewrite /snapshot_inv.
        set (<[ (v'' + 1)%Z := x2]> T) as T'.
        iExists l1'new, T', x2, (v'' + 1)%Z.
        iFrame.
        iPureIntro. split.
        * apply: lookup_insert_eq.
        * intros t' Hv. destruct (decide (t' = (v'' + 1)%Z)) as [-> | Hn]; first done.
          assert (dom T' = {[(v'' + 1)%Z]} ∪ dom T) as Hd. {
            apply leibniz_equiv. rewrite dom_insert. done.
          }
          rewrite Hd in Hv. clear Hd. apply elem_of_union in Hv.
          destruct Hv as [Hv%elem_of_singleton_1 | Hv]; first done.
          specialize (Hvt _ Hv). lia.
      + wp_pures. done.
    - wp_cmpxchg_fail. iModIntro. iSplitR "AU".
      + iNext. rewrite /snapshot_inv. eauto 10 with iFrame.
      + wp_pures. iApply "IH"; last eauto. rewrite /is_snapshot. eauto.
  Qed.

  Lemma read_spec γ p :
    is_snapshot γ p -∗
    <<{ ∀∀ v : val, snapshot_content γ v }>>
      read p @ ↑N
    <<{ snapshot_content γ v | RET v }>>.
  Proof.
    iIntros "Hx". iIntros (Φ) "AU".
    iDestruct "Hx" as (l1 ->) "#Hinv".
    wp_lam. wp_bind (! #l1)%E.
    (* open invariant for 1st read *)
    iInv N as (l1' T x v') ">[Hl1 [#Hl1' [Hx⚫ Htime]]]".
      wp_load.
      iMod "AU" as (xv) "[Hx [_ Hclose]]".
      iDestruct (excl_sync with "Hx⚫ Hx") as %[= ->].
      iMod ("Hclose" with "Hx") as "HΦ".
      (* close invariant *)
      iModIntro. iSplitR "HΦ Hl1'". {
        iNext. unfold snapshot_inv. eauto 7 with iFrame.
      }
    iApply wp_fupd. wp_load. wp_pures. eauto.
  Qed.

  Definition prophecy_to_bool (v : list (val * val)) : bool :=
    match v with
    | (_, LitV (LitBool b)) :: _ => b
    | _                          => false
    end.

  Lemma read_with_spec γ p (l : loc) :
    is_snapshot γ p -∗
    <<{ ∀∀ v1 v2 : val, snapshot_content γ v1 ∗ l ↦ v2 }>>
       read_with_proph p #l @ ↑N
    <<{ snapshot_content γ v1 ∗ l ↦ v2 | RET (v1, v2) }>>.
  Proof.
    iIntros "Hx". iIntros (Φ) "AU". iLöb as "IH". wp_lam. wp_pures.
    (* ************ new prophecy ********** *)
    wp_apply wp_new_proph; first done.
    iIntros (proph_val proph) "Hpr".
    wp_pures.
    (* ************ 1st readX ********** *)
    iDestruct "Hx" as (l1 ->) "#Hinv". wp_bind (! #l1)%E.
    (* open invariant for 1st read *)
    iInv N as (l1' T_x x1 v_x1) ">[Hl1 [#Hl1' [Hx⚫ [Ht_x Htime_x]]]]".
      iDestruct "Htime_x" as %[Hlookup_x Hdom_x].
      wp_load.
      iMod "AU" as (xv yv) "[[Hx Hy] [Hclose _]]".
      iDestruct (excl_sync with "Hx⚫ Hx") as %[= ->].
      iMod ("Hclose" with "[$Hx $Hy]") as "AU".
      (* duplicate timestamp T_x1 *)
      iMod (timestamp_dupl with "Ht_x") as "[Ht_x1⚫ Ht_x1◯]".
      (* close invariant *)
      iModIntro. iSplitR "AU Hl1' Ht_x1◯ Hpr". {
        iNext. unfold snapshot_inv. eauto 8 with iFrame.
      }
    wp_load. wp_let.
    (* ************ readY ********** *)
    repeat (wp_lam; wp_pures). wp_bind (!_)%E.
    iInv N as (l1'_y T_y x_y v_y) ">[Hl1 [#Hl1'_y [Hx⚫ [Ht_y Htime_y]]]]".
    iDestruct "Htime_y" as %[Hlookup_y Hdom_y].
    (* linearization point *)
    clear yv.
    iMod "AU" as (xv yv) "[[Hx Hy] Hclose]".
    wp_load.
    rewrite /snapshot_content.
    iDestruct (excl_sync with "Hx⚫ Hx") as %[= ->].
    destruct (prophecy_to_bool proph_val) eqn:Hproph.
    - (* prophecy value is predicting that timestamp has not changed, so we commit *)
      (* committing AU *)
      iMod ("Hclose" with "[$Hx $Hy]") as "HΦ".
      (* duplicate timestamp T_y *)
      iMod (timestamp_dupl with "Ht_y") as "[Ht_y● Ht_y◯]".
      (* show that T_x <= T_y *)
      iDestruct (timestamp_sub with "[Ht_y● Ht_x1◯]") as "%Hs"; first by iFrame.
      iModIntro. iModIntro.
      (* closing invariant *)
      iSplitR "HΦ Hl1' Ht_x1◯ Ht_y◯ Hpr".
      { iNext. unfold snapshot_inv. eauto 10 with iFrame. }
      wp_let.
      (* ************ 2nd readX ********** *)
      repeat (wp_lam; wp_pures). wp_bind (! #l1)%E.
      (* open invariant *)
      iInv N as (l1'_x2 T_x2 x2 v_x2) ">[Hl1 [#Hl1'_x2 [Hx⚫ [Ht_x2 Htime_x2]]]]".
      iDestruct "Htime_x2" as %[Hlookup_x2 Hdom_x2].
      wp_load.
      (* show that T_y <= T_x2 *)
      iDestruct (timestamp_sub with "[Ht_x2 Ht_y◯]") as "%Hs'"; first by iFrame.
      iModIntro. iSplitR "HΦ Hpr". {
        iNext. unfold snapshot_inv. eauto 8 with iFrame.
      }
      wp_load. wp_pures.
      case_bool_decide as Heq; wp_apply (wp_resolve_proph with "Hpr");
        iIntros (vs') "[Eq _]"; iDestruct "Eq" as %->; wp_seq; wp_if.
      + inversion Heq; subst; clear Heq. wp_pures.
        assert (v_x2 = v_y) as ->. {
          assert (v_x2 ≤ v_y)%Z as vneq. {
            apply Hdom_y.
            eapply (iffRL (elem_of_dom T_y _)). eauto using mk_is_Some.
          }
          assert (v_y ≤ v_x2)%Z as vneq'. {
            apply Hdom_x2.
            eapply (iffRL (elem_of_dom T_x2 _)). eauto using mk_is_Some.
          }
          apply Z.le_antisymm; auto.
        }
        assert (x1 = x_y) as ->. {
          specialize (Hs _ _ Hlookup_x). rewrite Hs in Hlookup_y. inversion Hlookup_y. done.
        }
        done.
      + inversion Hproph.
    - (* prophecy value is predicting that timestamp has not changed, so we abort *)
      iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "[$Hx $Hy]") as "AU".
      iModIntro. iModIntro.
      (* closing invariant *)
      iSplitR "AU Hpr".
      { iNext. unfold snapshot_inv. eauto 10 with iFrame. }
      wp_let.
      (* ************ 2nd readX ********** *)
      wp_bind (! #l1)%E.
      (* open invariant *)
      iInv N as (l1'_x2 T_x2 x2 v_x2) "[Hl1 [#Hl1'_x2 [Hx⚫ [Ht_x2 Htime_x2]]]]".
      wp_load.
      iModIntro. iSplitR "AU Hpr". {
        iNext. unfold snapshot_inv. eauto 8 with iFrame.
      }
      wp_load. wp_pures.
      wp_apply (wp_resolve_proph with "Hpr").
      iIntros (vs') "[Heq _]"; iDestruct "Heq" as %->.
      case_bool_decide as Heq.
      + inversion Heq; subst; clear Heq. inversion Hproph.
      + wp_seq. wp_if. iApply "IH"; rewrite /is_snapshot; eauto.
  Qed.

End atomic_snapshot.

Program Definition atomic_snapshot `{!heapGS Σ, atomic_snapshotG Σ} :
  spec.atomic_snapshot Σ :=
  {| spec.new_snapshot_spec := new_snapshot_spec;
     spec.write_spec := write_spec;
     spec.read_spec := read_spec;
     spec.read_with_spec := read_with_spec;
     spec.snapshot_content_exclusive := snapshot_content_exclusive |}.

Global Typeclasses Opaque snapshot_content is_snapshot.
