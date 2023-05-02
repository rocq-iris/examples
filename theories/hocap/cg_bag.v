(** Concurrent bag specification from the HOCAP paper.
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

Coarse-grained implementation of a bag
*)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import cmra agree frac.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris_examples.hocap Require Import abstract_bag.
From iris.prelude Require Import options.

(** Coarse-grained bag implementation using a spin lock *)
Definition newBag : val := λ: <>,
  let: "r" := ref NONE in
  let: "l" := newlock #() in
  ("r", "l").
Definition pushBag : val := λ: "b" "v",
  let: "l" := Snd "b" in
  let: "r" := Fst "b" in
  acquire "l";;
  let: "t" := !"r" in
  "r" <- SOME ("v", "t");;
  release "l".
Definition popBag : val := λ: "b",
  let: "l" := Snd "b" in
  let: "r" := Fst "b" in
  acquire "l";;
  let: "v" := match: !"r" with
                NONE => NONE
              | SOME "s" =>
                "r" <- Snd "s";;
                SOME (Fst "s")
              end in
  release "l";;
  "v".

Canonical Structure valmultisetO := leibnizO (gmultiset valO).
Class bagG Σ := BagG
{ bag_bagG :: inG Σ (prodR fracR (agreeR valmultisetO));
  lock_bagG :: lockG Σ
}.

(** Generic specification for the bag, using view shifts. *)
Section proof.
  Context `{heapGS Σ, bagG Σ}.
  Variable N : namespace.

  Fixpoint bag_of_val (ls : val) : gmultiset val :=
    match ls with
    | NONEV => ∅
    | SOMEV (v1, t) => {[+ v1 +]} ⊎ bag_of_val t
    | _ => ∅
    end.
  Fixpoint val_of_list (ls : list val) : val :=
    match ls with
    | [] => NONEV
    | x::xs => SOMEV (x, val_of_list xs)
    end.

  Definition bag_inv (γb : gname) (b : loc) : iProp Σ :=
    (∃ ls : list val, b ↦ (val_of_list ls) ∗ own γb ((1/2)%Qp, to_agree (list_to_set_disj ls)))%I.
  Definition is_bag (γb : gname) (x : val) :=
    (∃ (lk : val) (b : loc) (γ : gname),
        ⌜x = PairV #b lk⌝ ∗ is_lock γ lk (bag_inv γb b))%I.
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
    wp_alloc r as "Hr". wp_let.
    iMod (own_alloc (1%Qp, to_agree ∅)) as (γb) "[Ha Hf]"; first done.
    wp_apply (newlock_spec (bag_inv γb r) with "[Hr Ha]").
    { iExists []. iFrame. }
    iIntros (lk γ) "#Hlk". wp_pures. iApply "HΦ".
    rewrite /is_bag /bag_contents. iFrame.
    iExists _,_,_. by iFrame "Hlk".
  Qed.

  Local Opaque acquire release. (* so that wp_pure doesn't stumble *)
  Lemma pushBag_spec (P Q : iProp Σ) γ (x v : val)  :
    □ (∀ (X : gmultiset val), bag_contents γ X ∗ P
                     ={⊤∖↑N}=∗ ▷ (bag_contents γ ({[+ v +]} ⊎ X) ∗ Q)) -∗
    {{{ is_bag γ x ∗ P }}}
      pushBag x (of_val v)
    {{{ RET #(); Q }}}.
  Proof.
    iIntros "#Hvs".
    iIntros (Φ). iModIntro. iIntros "[#Hbag HP] HΦ".
    unfold pushBag. wp_rec. wp_let.
    rewrite /is_bag /bag_inv.
    iDestruct "Hbag" as (lk b γl) "[% #Hlk]"; simplify_eq/=.
    repeat wp_pure _.
    wp_apply (acquire_spec with "Hlk"). iIntros "[Htok Hb1]".
    iDestruct "Hb1" as (ls) "[Hb Ha]".
    wp_seq. wp_load. wp_let.
    wp_bind (_ <- _)%E.
    iApply (wp_mask_mono _ (⊤∖↑N)); first done.
    iMod ("Hvs" with "[$Ha $HP]") as "[Hbc HQ]".
    wp_store. iModIntro. wp_seq.
    wp_apply (release_spec with  "[$Hlk $Htok Hbc Hb]").
    { iExists (v::ls); iFrame. }
    iIntros "_". by iApply "HΦ".
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
    unfold popBag. wp_rec.
    rewrite /is_bag /bag_inv.
    iDestruct "Hbag" as (lk b γl) "[% #Hlk]"; simplify_eq/=.
    repeat wp_pure _.
    wp_apply (acquire_spec with "Hlk"). iIntros "[Htok Hb1]".
    iDestruct "Hb1" as (ls) "[Hb Ha]".
    wp_seq. wp_bind (!#b)%E.
    iApply (wp_mask_mono _ (⊤∖↑N)); first done.
    destruct ls as [|v ls]; simpl.
    - iMod ("Hvs2" with "[$Ha $HP]") as "[Hbc HQ]".
      wp_load. iModIntro. wp_pures.
      wp_apply (release_spec with  "[$Hlk $Htok Hbc Hb]").
      { iExists []; iFrame. }
      iIntros "_". repeat wp_pure _. by iApply "HΦ".
    - iMod ("Hvs1" with "[$Ha $HP]") as "[Hbc HQ]".
      wp_load. iModIntro. wp_store. wp_pures.
      wp_apply (release_spec with  "[$Hlk $Htok Hbc Hb]").
      { iExists ls; iFrame. }
      iIntros "_". repeat wp_pure _. by iApply "HΦ".
  Qed.

End proof.

Global Typeclasses Opaque bag_contents is_bag.

Definition cg_bag `{!heapGS Σ, !bagG Σ} : bag Σ :=
  {| abstract_bag.is_bag N := is_bag;
     abstract_bag.is_bag_persistent N := is_bag_persistent;
     abstract_bag.bag_contents_timeless := bag_contents_timeless;
     abstract_bag.bag_contents_agree := bag_contents_agree;
     abstract_bag.bag_contents_update := bag_contents_update;
     abstract_bag.newBag_spec N := newBag_spec;
     abstract_bag.pushBag_spec := pushBag_spec;
     abstract_bag.popBag_spec := popBag_spec |}.
