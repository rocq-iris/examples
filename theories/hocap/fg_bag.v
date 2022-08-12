(** Concurrent bag specification from the HOCAP paper.
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

Fine-grained implementation of a bag
*)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import cmra agree frac.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris_examples.hocap Require Import abstract_bag.
From iris.prelude Require Import options.

(** Fine-grained bag implementation using CAS *)
Definition newBag : val := λ: <>,
  ref NONE.
Definition pushBag : val := rec: "push" "b" "v" :=
  let: "oHead" := !"b" in
  if: CAS "b" "oHead" (SOME (ref ("v", "oHead")))
  then #()
  else "push" "b" "v".

Definition popBag : val := rec: "pop" "b" :=
  match: !"b" with
    NONE => NONE
  | SOME "l" =>
    let: "hd" := !"l" in
    let: "v" := Fst "hd" in
    let: "tl" := Snd "hd" in
    if: CAS "b" (SOME "l") "tl"
    then SOME "v"
    else "pop" "b"
  end.

Canonical Structure valmultisetO := leibnizO (gmultiset valO).
Class bagG Σ := BagG
{ bag_bagG :> inG Σ (prodR fracR (agreeR valmultisetO));
}.

(** Generic specification for the bag, using view shifts. *)
Section proof.
  Context `{heapGS Σ, bagG Σ}.
  Variable N : namespace.

  Definition oloc_to_val (ol: option loc) : val :=
    match ol with
    | None => NONEV
    | Some loc => SOMEV (#loc)
    end.
  Local Instance oloc_to_val_inj : Inj (=) (=) oloc_to_val.
  Proof. intros [|][|]; simpl; congruence. Qed.

  Fixpoint is_list (hd : option loc) (xs : list val) : iProp Σ :=
    match xs, hd with
    | [], None => True
    | x::xs, Some l => ∃ (tl : option loc),
                   l ↦□ (x, oloc_to_val tl) ∗ is_list tl xs
    | _, _ => False
    end%I.

  Lemma is_list_duplicate hd xs : is_list hd xs -∗ is_list hd xs ∗ is_list hd xs.
  Proof.
    iInduction xs as [ | x xs ] "IH" forall (hd); simpl; eauto.
    destruct hd; last by auto.
    iDestruct 1 as (tl) "[#Hro Htl]".
    iDestruct ("IH" with "Htl") as "[Htl Htl']".
    iSplitL "Hro Htl"; iExists _; iFrame; eauto.
  Qed.

  Lemma is_list_agree hd xs ys : is_list hd xs -∗ is_list hd ys -∗ ⌜xs = ys⌝.
  Proof.
    iInduction xs as [ | x xs ] "IH" forall (hd ys); simpl; eauto.
    - destruct hd; first by auto.
      destruct ys; eauto.
    - destruct hd; last by auto.
      destruct ys as [| y ys]; eauto. simpl.
      iDestruct 1 as (tl) "(Hro & Hls)".
      iDestruct 1 as (tl') "(Hro' & Hls')".
      iDestruct (mapsto_agree with "Hro Hro'") as %?; simplify_eq/=.
      iDestruct ("IH" with "Hls Hls'") as %->. done.
  Qed.

  Definition bag_inv (γb : gname) (b : loc) : iProp Σ :=
    (∃ (hd : option loc) (ls : list val),
        b ↦ oloc_to_val hd ∗ is_list hd ls ∗ own γb ((1/2)%Qp, to_agree (list_to_set_disj ls)))%I.
  Definition is_bag (γb : gname) (x : val) :=
    (∃ (b : loc), ⌜x = #b⌝ ∗ inv N (bag_inv γb b))%I.
  Definition bag_contents (γb : gname) (X : gmultiset val) : iProp Σ :=
    own γb ((1/2)%Qp, to_agree X).

  Global Instance is_bag_persistent γb x : Persistent (is_bag γb x).
  Proof. apply _. Qed.
  Global Instance bag_contents_timeless γb X : Timeless (bag_contents γb X).
  Proof. apply _. Qed.

  Lemma bag_contents_agree γb X Y :
    bag_contents γb X -∗ bag_contents γb Y -∗ ⌜X = Y⌝.
  Proof.
    rewrite /bag_contents. apply bi.wand_intro_r.
    rewrite -own_op own_valid uPred.discrete_valid.
    f_equiv=> /=. rewrite -pair_op.
    by intros [_ ?%to_agree_op_inv_L].
  Qed.

  Lemma bag_contents_update γb X X' Y :
    bag_contents γb X ∗ bag_contents γb X' ==∗ bag_contents γb Y ∗ bag_contents γb Y.
  Proof.
    iIntros "[Hb1 Hb2]".
    iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
    iMod (own_update_2 with "Hb1 Hb2") as "Hb".
    { rewrite -pair_op frac_op.
      assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp.div_2.
      by apply (cmra_update_exclusive (1%Qp, to_agree Y)). }
    iDestruct "Hb" as "[Hb1 Hb2]".
    rewrite /bag_contents. by iFrame.
  Qed.

  Lemma newBag_spec :
    {{{ True }}}
      newBag #()
    {{{ x γ, RET x; is_bag γ x ∗ bag_contents γ ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    unfold newBag. wp_rec.
    wp_alloc r as "Hr".
    iMod (own_alloc (1%Qp, to_agree ∅)) as (γb) "[Ha Hf]"; first done.
    iMod (inv_alloc N _ (bag_inv γb r) with "[Ha Hr]") as "#Hinv".
    { iNext. iExists None,[]. simpl. iFrame. }
    iModIntro. iApply "HΦ".
    rewrite /is_bag /bag_contents. iFrame.
    iExists _. by iFrame "Hinv".
  Qed.

  Lemma pushBag_spec (P Q : iProp Σ) γ (x v : val)  :
    □ (∀ (X : gmultiset val), bag_contents γ X ∗ P
                     ={⊤∖↑N}=∗ ▷ (bag_contents γ ({[+ v +]} ⊎ X) ∗ Q)) -∗
    {{{ is_bag γ x ∗ P }}}
      pushBag x (of_val v)
    {{{ RET #(); Q }}}.
  Proof.
    iIntros "#Hvs".
    iIntros (Φ). iModIntro. iIntros "[#Hbag HP] HΦ".
    unfold pushBag.
    iLöb as "IH". wp_rec. wp_pures.
    rewrite /is_bag.
    iDestruct "Hbag" as (b) "[% #Hinv]"; simplify_eq/=.
    wp_bind (! #b)%E.
    iInv N as (o ls) "[Ho [Hls >Hb]]" "Hcl".
    wp_load.
    iMod ("Hcl" with "[Ho Hls Hb]") as "_".
    { iNext. iExists _,_. iFrame. } clear ls.
    iModIntro.
    wp_alloc n as "Hn".
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (o' ls) "[Ho [Hls >Hb]]" "Hcl".
    destruct (decide (o = o')) as [->|?].
    - wp_cmpxchg_suc. { destruct o'; left; done. }
      iMod (mapsto_persist with "Hn") as "#Hn".
      iMod ("Hvs" with "[$Hb $HP]") as "[Hb HQ]".
      iMod ("Hcl" with "[Ho Hn Hls Hb]") as "_".
      { iNext. iExists (Some _),(v::ls). iFrame "Ho Hb".
        simpl. iExists _. by iFrame. }
      iModIntro. wp_pures. by iApply "HΦ".
    - wp_cmpxchg_fail.
      { destruct o, o'; simpl; congruence. }
      { destruct o'; left; done. }
      iMod ("Hcl" with "[Ho Hls Hb]") as "_".
      { iNext. iExists _,ls. by iFrame "Ho Hb". }
      iModIntro. wp_proj. wp_if.
      by iApply ("IH" with "HP [HΦ]").
  Qed.

  Lemma popBag_spec (P : iProp Σ) (Q : val → iProp Σ) γ x :
    □ (∀ (X : gmultiset val) (y : val),
               bag_contents γ ({[+ y +]} ⊎ X) ∗ P
               ={⊤∖↑N}=∗ ▷ (bag_contents γ X ∗ Q (SOMEV y))) -∗
    □ (bag_contents γ ∅ ∗ P ={⊤∖↑N}=∗ ▷ (bag_contents γ ∅ ∗ Q NONEV)) -∗
    {{{ is_bag γ x ∗ P }}}
      popBag x
    {{{ v, RET v; Q v }}}.
  Proof.
    iIntros "#Hvs1 #Hvs2".
    iIntros (Φ). iModIntro. iIntros "[#Hbag HP] HΦ".
    unfold popBag.
    iLöb as "IH". wp_rec.
    rewrite /is_bag.
    iDestruct "Hbag" as (b) "[% #Hinv]"; simplify_eq/=.
    wp_bind (!#b)%E.
    iInv N as (o ls) "[Ho [Hls >Hb]]" "Hcl".
    wp_load.
    destruct ls as [|x ls]; simpl.
    - destruct o; first done.
      iMod ("Hvs2" with "[$Hb $HP]") as "[Hb HQ]".
      iMod ("Hcl" with "[Ho Hb]") as "_".
      { iNext. iExists _,[]. by iFrame. }
      iModIntro. repeat wp_pure _.
      by iApply "HΦ".
    - destruct o as [hd|]; last done.
      iDestruct "Hls" as (tl) "[#Hhd Hls]"; simplify_eq/=.
      rewrite is_list_duplicate. iDestruct "Hls" as "[Hls Hls']".
      iMod ("Hcl" with "[Ho Hb Hhd Hls]") as "_".
      { iNext. iExists (Some _),(x::ls). simpl; iFrame; eauto. }
      iModIntro. repeat wp_pure _.
      wp_load. wp_pures.
      wp_bind (CmpXchg _ _ _).
      iInv N as (o' ls') "[Ho [Hls >Hb]]" "Hcl".
      destruct (decide (o' = (Some hd))) as [->|?].
      + wp_cmpxchg_suc.
        (* The list is still the same *)
        rewrite (is_list_duplicate tl). iDestruct "Hls'" as "[Hls' Htl]".
        iAssert (is_list (Some hd) (x::ls)) with "[Hhd Hls']" as "Hls'".
        { simpl. iExists tl. by iFrame. }
        iDestruct (is_list_agree with "Hls Hls'") as %?. simplify_eq.
        iClear "Hls'".
        iDestruct "Hls" as (tl') "(Hro' & Htl')".
        iMod ("Hvs1" with "[$Hb $HP]") as "[Hb HQ]".
        iMod ("Hcl" with "[Ho Htl Hb]") as "_".
        { iNext. iExists _,ls. by iFrame "Ho Hb". }
        iModIntro. wp_pures. by iApply "HΦ".
      + wp_cmpxchg_fail. { destruct o'; simpl; congruence. }
        iMod ("Hcl" with "[Ho Hls Hb]") as "_".
        { iNext. iExists _,ls'. by iFrame "Ho Hb". }
        iModIntro. wp_proj. wp_if.
        by iApply ("IH" with "HP [HΦ]").
  Qed.
End proof.

Global Typeclasses Opaque bag_contents is_bag.

Definition cg_bag `{!heapGS Σ, !bagG Σ} : bag Σ :=
  {| abstract_bag.is_bag := is_bag;
     abstract_bag.is_bag_persistent := is_bag_persistent;
     abstract_bag.bag_contents_timeless := bag_contents_timeless;
     abstract_bag.bag_contents_agree := bag_contents_agree;
     abstract_bag.bag_contents_update := bag_contents_update;
     abstract_bag.newBag_spec := newBag_spec;
     abstract_bag.pushBag_spec := pushBag_spec;
     abstract_bag.popBag_spec := popBag_spec |}.
