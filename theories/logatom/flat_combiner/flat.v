(* Flat Combiner *)
From iris.algebra Require Import auth frac agree excl agree gset gmap.
From iris.base_logic Require Import saved_prop invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris_examples.logatom.flat_combiner Require Import misc peritem sync.
From iris.prelude Require Import options.

Set Default Proof Using "Type*".

Definition doOp : val :=
  λ: "p",
     match: !"p" with
       InjL "req" => "p" <- InjR ((Fst "req") (Snd "req"))
     | InjR "_" => #()
     end.

Definition try_srv : val :=
  λ: "lk" "s",
    if: try_acquire "lk"
      then let: "hd" := !"s" in
           treiber.iter "hd" doOp;;
           release "lk"
      else #().

Definition loop: val :=
  rec: "loop" "p" "s" "lk" :=
    match: !"p" with
    InjL "_" =>
        try_srv "lk" "s";;
        "loop" "p" "s" "lk"
    | InjR "r" => "r"
    end.

Definition install : val :=
  λ: "f" "x" "s",
     let: "p" := ref (InjL ("f", "x")) in
     push "s" "p";;
     "p".

Definition mk_flat : val :=
  λ: <>,
   let: "lk" := newlock #() in
   let: "s" := new_stack #() in
   λ: "f" "x",
      let: "p" := install "f" "x" "s" in
      let: "r" := loop "p" "s" "lk" in
      "r".

Definition reqR := prodR fracR (agreeR valO). (* request x should be kept same *)
Definition toks : Type := gname * gname * gname * gname * gname. (* a bunch of tokens to do state transition *)
Class flatG Σ := FlatG {
  req_G :: inG Σ reqR;
  sp_G  :: savedPredG Σ val;
  tok_G :: inG Σ (exclR unitO);
}.

Definition flatΣ : gFunctors :=
  #[ GFunctor (constRF reqR);
     GFunctor (exclR unitO);
     savedPredΣ val ].

Global Instance subG_flatΣ {Σ} : subG flatΣ Σ → flatG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !lockG Σ, !flatG Σ} (N: namespace).

  Definition init_s (ts: toks) :=
    let '(_, γ1, γ3, _, _) := ts in (own γ1 (Excl ()) ∗ own γ3 (Excl ()))%I.

  Definition installed_s R (ts: toks) (f x: val) :=
    let '(γx, γ1, _, γ4, γq) := ts in
    (∃ (P: val → iProp Σ) Q,
       own γx ((1/2)%Qp, to_agree x) ∗ P x ∗ ({{{ R ∗ P x }}} f x {{{ v, RET v; R ∗ Q x v }}}) ∗
       saved_pred_own γq DfracDiscarded (Q x) ∗ own γ1 (Excl ()) ∗ own γ4 (Excl ()))%I.

  Definition received_s (ts: toks) (x: val) γr :=
    let '(γx, _, _, γ4, _) := ts in
    (own γx ((1/2/2)%Qp, to_agree x) ∗ own γr (Excl ()) ∗ own γ4 (Excl ()))%I.

  Definition finished_s (ts: toks) (x y: val) :=
    let '(γx, γ1, _, γ4, γq) := ts in
    (∃ Q: val → val → iProp Σ,
       own γx ((1/2)%Qp, to_agree x) ∗ saved_pred_own γq DfracDiscarded (Q x) ∗
       Q x y ∗ own γ1 (Excl ()) ∗ own γ4 (Excl ()))%I.

  Definition p_inv R (γm γr: gname) (ts: toks) (p : loc) :=
    ( (* INIT *)
      (∃ y: val, p ↦ InjRV y ∗ init_s ts) ∨
      (* INSTALLED *)
      (∃ f x: val, p ↦ InjLV (f, x) ∗ installed_s R ts f x) ∨
      (* RECEIVED *)
      (∃ f x: val, p ↦ InjLV (f, x) ∗ received_s ts x γr) ∨
      (* FINISHED *)
      (∃ x y: val, p ↦ InjRV y ∗ finished_s ts x y))%I.

  Definition p_inv' R γm γr : val → iProp Σ :=
    (λ v: val, ∃ ts (p: loc), ⌜v = #p⌝ ∗ inv N (p_inv R γm γr ts p))%I.

  Definition srv_bag R γm γr s := (∃ xs, is_bag_R N (p_inv' R γm γr) xs s)%I.

  Definition installed_recp (ts: toks) (x: val) (Q: val → iProp Σ) :=
    let '(γx, _, γ3, _, γq) := ts in
    (own γ3 (Excl ()) ∗ own γx ((1/2)%Qp, to_agree x) ∗ saved_pred_own γq DfracDiscarded Q)%I.

  Lemma install_spec R P Q (f x: val) (γm γr: gname) (s: loc):
    {{{ inv N (srv_bag R γm γr s) ∗ P ∗ ({{{ R ∗ P }}} f x {{{ v, RET v; R ∗ Q v }}}) }}}
      install f x #s
    {{{ p ts, RET #p; installed_recp ts x Q ∗ inv N (p_inv R γm γr ts p) }}}.
  Proof.
    iIntros (Φ) "(#? & HP & Hf) HΦ".
    wp_lam. wp_pures. wp_alloc p as "Hl".
    iApply fupd_wp.
    iMod (own_alloc (Excl ())) as (γ1) "Ho1"; first done.
    iMod (own_alloc (Excl ())) as (γ3) "Ho3"; first done.
    iMod (own_alloc (Excl ())) as (γ4) "Ho4"; first done.
    iMod (own_alloc (1%Qp, to_agree x)) as (γx) "Hx"; first done.
    iMod (saved_pred_alloc Q) as (γq) "#?"; first done.
    iDestruct (own_update with "Hx") as ">[Hx1 Hx2]"; first by apply pair_l_frac_op_1'.
    iModIntro. wp_let. wp_bind (push _ _).
    iMod (inv_alloc N _ (p_inv R γm γr (γx, γ1, γ3, γ4, γq) p)
          with "[-HΦ Hx2 Ho3]") as "#HRx"; first eauto.
    { iNext. iRight. iLeft. iExists f, x. iFrame.
      iExists (λ _, P), (λ _ v, Q v).
      iFrame. iFrame "#". }
    iApply (push_spec N (p_inv' R γm γr) s #p
            with "[-HΦ Hx2 Ho3]")=>//.
    { iFrame "#". iExists (γx, γ1, γ3, γ4, γq), p.
      iSplitR; first done. iFrame "#". }
    iNext. iIntros "?".
    wp_seq. iApply ("HΦ" $! p (γx, γ1, γ3, γ4, γq)).
    iFrame. by iFrame "#".
  Qed.

  Lemma doOp_f_spec R γm γr (p: loc) ts:
    f_spec N (p_inv R γm γr ts p) doOp (own γr (Excl ()) ∗ R)%I #p.
  Proof.
    iIntros (Φ) "(#H1 & Hor & HR) HΦ".
    wp_rec. wp_bind (! _)%E.
    iInv N as "Hp" "Hclose".
    iDestruct "Hp" as "[Hp | [Hp | [Hp | Hp]]]"; subst.
    - iDestruct "Hp" as (y) "[>Hp Hts]".
      wp_load. iMod ("Hclose" with "[-Hor HR HΦ]").
      { iNext. iFrame "#". iLeft. iExists y. iFrame. }
      iModIntro. wp_match. iApply ("HΦ" with "[Hor HR]"). iFrame.
    - destruct ts as [[[[γx γ1] γ3] γ4] γq].
      iDestruct "Hp" as (f x) "(>Hp & Hts)".
      iDestruct "Hts" as (P Q) "(>Hx & Hpx & Hf' & HoQ & >Ho1 & >Ho4)".
      iAssert (|==> own γx (((1/2/2)%Qp, to_agree x) ⋅
                            ((1/2/2)%Qp, to_agree x)))%I with "[Hx]" as ">[Hx1 Hx2]".
      { iDestruct (own_update with "Hx") as "?"; last by iAssumption.
        rewrite -{1}(Qp.div_2 (1/2)%Qp).
        by apply pair_l_frac_op'. }
      wp_load. iMod ("Hclose" with "[-Hf' Ho1 Hx2 HoQ HR HΦ Hpx]") as "_".
      { iNext. rewrite {2}/p_inv. iRight. iRight. iLeft. iExists f, x. iFrame. }
      iModIntro. wp_match. wp_pures.
      wp_bind (f _). iApply ("Hf'" with "[$HR $Hpx]").
      iIntros "!>" (v) "[HR HQ]". wp_pures.
      iInv N as "Hx" "Hclose".
      iDestruct "Hx" as "[Hp | [Hp | [Hp | Hp]]]"; subst.
      * iDestruct "Hp" as (?) "(_ & >Ho1' & _)".
        iApply excl_falso. iFrame.
      * iDestruct "Hp" as (? ?) "[>? Hs]". iDestruct "Hs" as (? ?) "(_ & _ & _ & _ & >Ho1' & _)".
        iApply excl_falso. iFrame.
      * iDestruct "Hp" as (? x5) ">(Hp & Hx & Hor & Ho4)".
        wp_store. iDestruct (m_frag_agree' with "Hx Hx2") as "[Hx %]".
        subst. rewrite Qp.div_2. iMod ("Hclose" with "[-HR Hor HΦ]").
        { iNext. iDestruct "Hp" as "[Hp1 Hp2]". iRight. iRight.
          iRight. iExists _, v. iFrame. iExists Q. iFrame. }
        iApply "HΦ". iFrame. done.
      * iDestruct "Hp" as (? ?) "[? Hs]". iDestruct "Hs" as (?) "(_ & _ & _ & >Ho1' & _)".
        iApply excl_falso. iFrame.
    - destruct ts as [[[[γx γ1] γ3] γ4] γq]. iDestruct "Hp" as (? x) "(_ & _ & >Ho2' & _)".
      iApply excl_falso. iFrame.
    - destruct ts as [[[[γx γ1] γ3] γ4] γq]. iDestruct "Hp" as (x' y) "[Hp Hs]".
        iDestruct "Hs" as (Q) "(>Hx & HoQ & HQxy & >Ho1 & >Ho4)".
        wp_load. iMod ("Hclose" with "[-HΦ HR Hor]").
        { iNext. iRight. iRight. iRight. iExists x', y. iFrame. iExists Q. iFrame. }
        iModIntro. wp_match. iApply "HΦ". by iFrame.
  Qed.

  Definition own_γ3 (ts: toks) := let '(_, _, γ3, _, _) := ts in own γ3 (Excl ()).
  Definition finished_recp (ts: toks) (x y: val) :=
    let '(γx, _, _, _, γq) := ts in
    (∃ Q, own γx ((1 / 2)%Qp, to_agree x) ∗ saved_pred_own γq DfracDiscarded (Q x) ∗ Q x y)%I.

  Lemma loop_iter_doOp_spec R (γm γr: gname) xs:
  ∀ (hd: loc),
    {{{ is_list_R N (p_inv' R γm γr) hd xs ∗ own γr (Excl ()) ∗ R }}}
      treiber.iter #hd doOp
    {{{ RET #(); own γr (Excl ()) ∗ R }}}.
  Proof.
    induction xs as [|x xs' IHxs].
    - iIntros (hd Φ) "[Hxs ?] HΦ".
      simpl. wp_rec. wp_let.
      wp_load. wp_match. by iApply "HΦ".
    - iIntros (hd Φ) "[Hxs HRf] HΦ". simpl.
      iDestruct "Hxs" as (hd') "(#Hhd & #Hinv & Hxs')".
      wp_rec. wp_let. wp_bind (! _)%E.
      iInv N as "H" "Hclose".
      iDestruct "H" as (ts p) "[>% #?]". subst.
      wp_load. iMod ("Hclose" with "[]").
      { iNext. iExists ts, p. eauto. }
      iModIntro. wp_match. wp_proj. wp_bind (doOp _).
      iDestruct (doOp_f_spec R γm γr p ts) as "Hf".
      iApply ("Hf" with "[HRf]").
      { iFrame. iFrame "#". }
      iNext. iIntros "HRf".
      wp_seq. wp_proj. iApply (IHxs with "[-HΦ]")=>//.
      iFrame "#"; first by iFrame.
  Qed.

  Lemma try_srv_spec R (s: loc) (lk: val) (γr γm γlk: gname) Φ :
    inv N (srv_bag R γm γr s) ∗
    is_lock γlk lk (own γr (Excl ()) ∗ R) ∗ Φ #()
    ⊢ WP try_srv lk #s {{ Φ }}.
  Proof.
    iIntros "(#? & #? & HΦ)". wp_lam. wp_pures.
    wp_bind (try_acquire _). iApply (try_acquire_spec with "[]"); first done.
    iNext. iIntros ([]); last by (iIntros; wp_if).
    iIntros "[Hlocked [Ho2 HR]]".
    wp_if. wp_bind (! _)%E.
    iInv N as "H" "Hclose".
    iDestruct "H" as (xs' hd') "[>Hs #Hxs]".
    wp_load.
    iMod ("Hclose" with "[Hs]").
    { iNext. iFrame. iExists xs', hd'. by iFrame. }
    iModIntro. wp_let. wp_bind (treiber.iter _ _).
    iApply wp_wand_r. iSplitL "HR Ho2".
    { iApply (loop_iter_doOp_spec R _ _ _ _ (λ _, own γr (Excl ()) ∗ R)%I with "[-]")=>//.
      - iFrame "#∗".
      - eauto. }
    iIntros (f') "[Ho HR]". wp_seq.
    iApply (release_spec with "[Hlocked Ho HR]"); first iFrame "#∗".
    iNext. iIntros. done.
  Qed.

  Lemma loop_spec R (p s: loc) (lk: val)
        (γs γr γm γlk: gname) (ts: toks):
    {{{ inv N (srv_bag R γm γr s) ∗ inv N (p_inv R γm γr ts p) ∗
        is_lock γlk lk (own γr (Excl ()) ∗ R) ∗ own_γ3 ts }}}
      loop #p #s lk
    {{{ x y, RET y; finished_recp ts x y }}}.
  Proof.
    iIntros (Φ) "(#? & #? & #? & Ho3) HΦ".
    iLöb as "IH". wp_rec. repeat wp_let.
    wp_bind (! _)%E. iInv N as "Hp" "Hclose".
    destruct ts as [[[[γx γ1] γ3] γ4] γq].
    iDestruct "Hp" as "[Hp | [Hp | [ Hp | Hp]]]".
    + iDestruct "Hp" as (?) "(_ & _ & >Ho3')".
      iApply excl_falso. iFrame.
    + iDestruct "Hp" as (f x) "(>Hp & Hs')".
      wp_load. iMod ("Hclose" with "[Hp Hs']").
      { iNext. iFrame. iRight. iLeft. iExists f, x. iFrame. }
      iModIntro. wp_match. wp_bind (try_srv _ _). iApply try_srv_spec=>//.
      iFrame "#". wp_seq. iApply ("IH" with "Ho3"); eauto.
    + iDestruct "Hp" as (f x) "(Hp & Hx & Ho2 & Ho4)".
      wp_load. iMod ("Hclose" with "[-Ho3 HΦ]") as "_".
      { iNext. (* FIXME: iFrame here divergses, with an enormous TC trace *)
        iRight. iRight. iLeft. iExists f, x. iFrame. }
      iModIntro. wp_match.
      wp_bind (try_srv _ _). iApply try_srv_spec=>//.
      iFrame "#". wp_seq. iApply ("IH" with "Ho3"); eauto.
    + iDestruct "Hp" as (x y) "[>Hp Hs']".
      iDestruct "Hs'" as (Q) "(>Hx & HoQ & HQ & >Ho1 & >Ho4)".
      wp_load. iMod ("Hclose" with "[-Ho4 HΦ Hx HoQ HQ]").
      { iNext. iLeft. iExists y. iFrame. }
      iModIntro. wp_match. iApply ("HΦ" with "[-]"). iFrame.
      iExists Q. iFrame.
  Qed.

  Lemma mk_flat_spec (γm: gname): mk_syncer_spec mk_flat.
  Proof using Type* N.
    iIntros (R Φ) "HR HΦ".
    iMod (own_alloc (Excl ())) as (γr) "Ho2"; first done.
    wp_lam. wp_bind (newlock _).
    iApply (newlock_spec (own γr (Excl ()) ∗ R)%I with "[$Ho2 $HR]")=>//.
    iNext. iIntros (lk γlk) "#Hlk".
    wp_let. wp_bind (new_stack _).
    iApply (new_bag_spec N (p_inv' R γm γr))=>//.
    iNext. iIntros (s) "#Hss".
    wp_pures. iModIntro. iApply "HΦ".
    iModIntro. iIntros (f). wp_pures.
    iIntros "!> !>" (P Q x) "#Hf !>".
    iIntros (Φ') "Hp HΦ'". wp_pures. wp_bind (install _ _ _).
    iApply (install_spec R P Q f x γm γr s with "[Hp]")=>//.
    { iFrame. iFrame "#". }
    iNext. iIntros (p [[[[γx γ1] γ3] γ4] γq]) "[(Ho3 & Hx & HoQ) #?]".
    wp_let. wp_bind (loop _ _ _).
    iApply (loop_spec with "[-Hx HoQ HΦ']")=>//.
    { iFrame "#". iFrame. }
    iNext. iIntros (v1 v2) "Hs".
    iDestruct "Hs" as (Q') "(Hx' & HoQ' & HQ')".
    destruct (decide (x = v1)) as [->|Hneq].
    - iDestruct (saved_pred_agree _ _ _ _ _ v2 with "[$HoQ] [HoQ']") as "Heq"; first by iFrame.
      wp_let. iApply "HΦ'". by iRewrite -"Heq" in "HQ'".
    - iExFalso. iCombine "Hx" "Hx'" as "Hx".
      iDestruct (own_valid with "Hx") as %[_ H1].
      rewrite //= in H1.
      by apply to_agree_op_inv in H1.
  Qed.

End proof.
