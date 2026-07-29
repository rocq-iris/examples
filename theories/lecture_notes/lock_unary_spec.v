(* This file contains the specification of a lock module discussed
   in the section on the Fancy update modality and weakest precondition
   in the Iris Lecture Notes. 
     Recall from loc. cit. that the point of this 
   alternative lock specification is that it allows ones
   to allocate the lock before one knows what the resource
   of the invariant it is going to protect is.
*)

(* Contains definitions of the weakest precondition assertion, and its basic rules. *)
From iris.program_logic Require Export weakestpre.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Export notation lang.

(* Files related to the interactive proof mode. The first import includes the
   general tactics of the proof mode. The second provides some more specialized
   tactics particular to the instantiation of Iris to a particular programming
   language. *)
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.

(* Definition of invariants and their rules (expressed using the fancy update
   modality). *)
From iris.base_logic.lib Require Export invariants.

(* The exclusive resource algebra *)
From iris.algebra Require Import excl.


Section lock_model.
(* In order to do the proof we need to assume certain things about the
   instantiation of Iris. The particular, even the heap is handled in an
   analogous way as other ghost state. This line states that we assume the Iris
   instantiation has sufficient structure to manipulate the heap, e.g., it
   allows us to use the points-to predicate, and that the ghost state includes
   the exclusive resource algebra over the singleton set (represented using the
   unitR type). *)

  Context `{heapGS Σ}.
  Context `{inG Σ (exclR unitR)}.

  (* We use a ghost name with a token to model whether the lock is locked or not.
     The the token is just exclusive ownerwhip of unit value. *)
  Definition locked γ := own γ (Excl ()).

  (* The name of a lock. *)
  Definition lockN (l : loc) := nroot .@ "lock" .@ l.

  (* The lock invariant *)
  Definition is_lock γ l P :=
    inv (lockN l) ((l ↦ (#false) ∗ P ∗ locked γ) ∨
                                l ↦ (#true))%I.

  (* The is_lock predicate is persistent *)
  Global Instance is_lock_persistent γ l Φ : Persistent (is_lock γ l Φ).
  Proof. apply _. Qed.

End lock_model.

Section lock_code.

  (* Here is the standard spin lock code *)

  Definition newlock : val := λ: <>, ref #false.
  Definition acquire : val :=
    rec: "acquire" "l" :=
      if: CAS "l" #false #true then #() else "acquire" "l".
  Definition release : val := λ: "l", "l" <- #false.

End lock_code.

Section lock_spec.
  Context `{heapGS Σ}.
  Context `{inG Σ (exclR unitR)}.

  (* Here is the interesting part of this example, namely the new specification
     for newlock, which allows one to get a post-condition which can be instantiated
     with the lock invariant at some point later, when it is known.
     See the discussion in Iris Lecture Notes.
     First we show the specs using triples, and afterwards using weakest preconditions.
  *)

  Lemma wp_newlock_t :
    {{{ True }}} newlock #() {{{v, RET v; ∃ (l: loc) γ, ⌜v = #l⌝ ∧ (∀ P E, P ={E}=∗ is_lock γ l P) }}}.
  Proof.
    iIntros (φ) "Hi Hcont".
    rewrite /newlock.
    wp_lam.
    wp_alloc l as "HPt".
    iApply "Hcont".
    iExists l.
    iMod (own_alloc (Excl ())) as (γ) "Hld"; first done.
    iExists γ.
    iModIntro. iSplit; first done.
    iIntros (P E) "HP".
    iMod (inv_alloc _ _
           ((l ↦ (#false) ∗ P ∗ locked γ) ∨ l ↦ (#true))%I with "[-]")
      as "Hinv"; last eauto.
    { iNext; iLeft; iFrame. }
  Qed.

  Lemma wp_acquire_t E γ l P :
    nclose (lockN l) ⊆ E →
    {{{ is_lock γ l P }}} acquire (#l) @ E {{{v, RET #v; P ∗ locked γ}}}.
  Proof.
    iIntros (HE φ) "#Hi Hcont"; rewrite /acquire.
    iLöb as "IH".
    wp_rec.
    wp_bind (CmpXchg _ _ _).
    iInv (lockN l) as "[(Hl & HP & Ht)|Hl]" "Hcl".
    - wp_cmpxchg_suc.
      iMod ("Hcl" with "[Hl]") as "_"; first by iRight.
      iModIntro.
      wp_proj.
      wp_if.
      iApply "Hcont".
      by iFrame.
    - wp_cmpxchg_fail.
      iMod ("Hcl" with "[Hl]") as "_"; first by iRight.
      iModIntro.
      wp_proj.
      wp_if.
      iApply ("IH" with "[$Hcont]").
  Qed.


  Lemma wp_release_t E γ l P :
    nclose (lockN l) ⊆ E →
    {{{ is_lock γ l P ∗ locked γ ∗ P }}} release (#l) @ E {{{RET #(); True}}}.
  Proof.
    iIntros (HE φ) "(#Hi & Hld & HP) Hcont"; rewrite /release.
    wp_lam.
    iInv (lockN l) as "[(Hl & HQ & >Ht)|Hl]" "Hcl".
    - iCombine "Hld Ht" gives %Hv. done.
    - wp_store.
      iMod ("Hcl" with "[-Hcont]") as "_"; first by iNext; iLeft; iFrame.
      iApply "Hcont".
      done.
  Qed.

  (* Here are the specifications again, just written using weakest preconditions *)

  Lemma wp_newlock :
    True ⊢ WP newlock #() {{v, ∃ (l: loc) γ, ⌜v = #l⌝ ∧ (∀ P E, P ={E}=∗ is_lock γ l P) }}.
  Proof.
    iIntros "_".
    rewrite /newlock.
    wp_lam.
    wp_alloc l as "HPt".
    iExists l.
    iMod (own_alloc (Excl ())) as (γ) "Hld"; first done.
    iExists γ.
    iModIntro. iSplit; first done.
    iIntros (P E) "HP".
    iMod (inv_alloc _ _
           ((l ↦ (#false) ∗ P ∗ locked γ) ∨ l ↦ (#true))%I with "[-]")
      as "Hinv"; last eauto.
    { iNext; iLeft; iFrame. }
  Qed.


  Lemma wp_acquire E γ l P :
    nclose (lockN l) ⊆ E →
    is_lock γ l P ⊢ WP acquire (#l) @ E {{v, P ∗ locked γ}}.
  Proof.
    iIntros (HE) "#Hi"; rewrite /acquire.
    iLöb as "IH".
    wp_rec.
    wp_bind (CmpXchg _ _ _).
    iInv (lockN l) as "[(Hl & HP & Ht)|Hl]" "Hcl".
    - wp_cmpxchg_suc.
      iMod ("Hcl" with "[Hl]") as "_"; first by iRight.
      iModIntro.
      wp_proj.
      wp_if.
      by iFrame.
    - wp_cmpxchg_fail.
      iMod ("Hcl" with "[Hl]") as "_"; first by iRight.
      iModIntro.
      wp_proj.
      wp_if.
      iApply "IH".
  Qed.


  Lemma wp_release E γ l P :
    nclose (lockN l) ⊆ E →
    is_lock γ l P ∗ locked γ ∗ P ⊢ WP release (#l) @ E {{v, True}}.
  Proof.
    iIntros (HE) "(#Hi & Hld & HP)"; rewrite /release.
    wp_lam.
    iInv (lockN l) as "[(Hl & HQ & >Ht)|Hl]" "Hcl".
    - iCombine "Hld Ht" gives %Hv. done.
    - wp_store.
      iMod ("Hcl" with "[-]") as "_"; first by iNext; iLeft; iFrame.
      done.
  Qed.


  Global Opaque newlock release acquire.

  (* We now present a simple client of the lock which cannot be verified with the
     lock specification described in the Chapter on Invariants and Ghost State in the
     Iris Lecture Notes, but which can be specifed and verified with the current 
     specification.
  *)
  Definition test : expr :=
    let: "l" := newlock #() in
    let: "r" := ref #0 in
    (λ: <>, acquire "l";; "r" <- !"r" + #1;; release "l").

  Lemma test_spec :
    {{{ True }}} test #() {{{ v, RET v; True }}}.
  Proof using Type*.
    iIntros (φ) "Hi HCont"; rewrite /test.
    wp_bind (newlock #())%E.
    iApply (wp_newlock_t); auto.
    iNext.
    iIntros (v) "Hs".
    wp_let.
    wp_bind (ref #0)%E.
    wp_alloc l as "Hl".
    wp_let.
    wp_seq.
    wp_bind (acquire v)%E.
    iDestruct "Hs" as (l' γ) "[% H2]".
    subst.
    iMod ("H2" $! (∃ (n : Z), l ↦ #n)%I with "[Hl]") as "#H3".
    { iExists 0; iFrame. }
    wp_apply (wp_acquire_t with "H3"); auto.
    iIntros (v) "(Hpt & Hlocked)".
    iDestruct "Hpt" as (u) "Hpt".
    wp_seq.
    wp_load.
    wp_op.
    wp_store.
    wp_apply (wp_release_t with "[-HCont]"); auto.
    iFrame "H3 Hlocked".
    iExists _; iFrame.
  Qed.
End lock_spec.

Global Typeclasses Opaque locked.
Global Opaque locked.
Global Typeclasses Opaque is_lock.
Global Opaque is_lock.
