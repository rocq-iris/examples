(* In this file we explain how to do prove the counter specifications from
   Section 8.7 of the notes. This involves construction and manipulation of
   resource algebras, the explanation of which is the focus of this file. We
   assume that the reader has experimented with coq_intro_example_1.v, and
   thus we do not explain the features we have already explained there.
 *)

From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.algebra Require Import numbers.
From iris.prelude Require Import options.

From iris.heap_lang.lib Require Import par.

(* The counter module definition. *)
Definition read : val := λ: "c", !"c".
Definition incr : val := rec: "incr" "c" := let: "n" := !"c" in
                                            let: "m" := #1 + "n" in
                                            if: CAS "c" "n" "m" then #() else "incr" "c".

Definition newCounter : val := λ: <>, ref #0.

Section monotone_counter.
  (* For the first example we will only give the weaker specification, as we did
     in the notes. In this specification we only know the lower bound on the
     counter value, since the isCounter predicate is freely duplicable.

     Before we start with the actual verification we will define the resource
     algebra we shall be using. The Iris library contains all the ingredients
     needed to compose this particular resource algebra from simpler components,
     however to illustrate how to define our own we will define it from scratch.

     In the subsequent section we show how to obtain an equivalent resource
     algebra from the building blocks provided by the Iris Coq library. 
  *)

  (* The carrier of our resource algebra is the set ℕ_{⊥,⊤} × ℕ. NBT (Natural
     numbers with Top and Bottom) is the first component of this product. We
     wrap the project into a record to avoid ambiguous type class search. *)
  Inductive NBT :=
    Bot : NBT (* Bottom *)
  | Top : NBT (* Top *)
  | NBT_incl : nat → NBT. (* Inclusion of natural numbers into our new type. *)

  (* The carrier of our RA. *)
  Record mcounterRAT := MCounter { mcounter_auth : NBT; mcounter_flag : nat }.

  (* The notion of a resource algebra as used in Iris is more general than the one
     currently described. It is called a cmra (standing roughly for complete
     metric resource algebra). For most verification purposes it is not
     important what that is. It is a step-indexed generalization of the resource
     algebra we have described in Section 7. The main difference is that the
     carrier is not simply a set, but comes equipped with a set of equivalence
     relations indexed by natural numbers (the "step-indices").

     The notion we have defined in Section 7 is that of a "discrete" CMRA. There
     is special support in the library for such CMRAs, and that is why in the
     remainder of this file we will often use, e.g., special lemmas for discrete
     CMRAs. 
   *)

  (* 
     To tell Coq we wish to use such a discrete CMRA we use the constructor leibnizO.
     This takes a Coq type and makes it an instance of an OFE (a step-indexed generalization of sets).
     This is not the place do describe Canonical Structures.
     A very good introduction is available at https://hal.inria.fr/hal-00816703v1/document 
  *)
  Canonical Structure mcounterRAC := leibnizO mcounterRAT.

  (* To make the type mcounterRAT into an RA we need an operation. This is
     defined in the standard way, except we use the typeclass Op so we can reuse
     a lot of the notation mechanism (we can write x ⋅ y for the operation), and
     some other infrastucture and generic lemmas. *)
  Local Instance mcounterRAop : Op mcounterRAT :=
    λ '(MCounter x n) '(MCounter y m),
    match x with
      Bot => MCounter y (max n m)
    | _ => match y with
             Bot => MCounter x (max n m)
           | _ => MCounter Top (max n m)
           end
    end.

  (* The set of valid elements. Valid A is simply abbreviation for A → Prop,
     i.e., for the set of subsets of A. Importantly Valid is a typeclass, and
     thus we make our definition an instance of it. This will enable the Coq
     typeclass search and various interactive proof mode tactics automatically
     deal with many boring use cases. *)
  Local Instance mcounterRAValid : Valid mcounterRAT :=
    λ x, match x with
           MCounter Bot _ => True
         | MCounter (NBT_incl x) m => x ≥ m
         | _ => False
         end.

  (* The core of the RA. PCore stands for "partial core", and is an abbreviation
     for a partial function, which in Coq is encoded as a function from A →
     option A. Again, PCore is a typeclass for better automation support, and
     thus our definition is an instance. *)
  Local Instance mcounterRACore : PCore mcounterRAT :=
    λ '(MCounter _ n), Some (MCounter Bot n).

  (* We can then package these definitions up into an RA structure, used by the
     Iris library. *)

  (* We need these auxiliary lemmas in the proof below. 
     We need the type  annotation to guide the type inference. *)
  Lemma mcounterRA_op_second (x y : NBT) n m :
    ∃ z, MCounter x n ⋅ MCounter y m = MCounter z (max n m).
  Proof.
    destruct x as [], y as []; eexists; unfold op, mcounterRAop; simpl; auto.
  Qed.

  Lemma mcounterRA_included_aux x y (n m : nat) :
    MCounter x n ≼ MCounter y m → (n ≤ m)%nat.
  Proof.
    intros [[z k] [=H]].
    revert H.
    destruct (mcounterRA_op_second x z n k) as [? ->].
    inversion 1; subst; auto with arith.
  Qed.

  Lemma mcounterRA_included_frag (n m : nat) :
    MCounter Bot n ≼ MCounter Bot m ↔ (n ≤ m)%nat.
  Proof.
    split.
    - apply mcounterRA_included_aux.
    - intros H%Nat.max_r; exists (MCounter Bot m); unfold op, mcounterRAop; rewrite H; auto.
  Qed.

  Lemma mcounterRA_valid x (n : nat): ✓ (MCounter (NBT_incl x) n) ↔ (n ≤ x)%nat.
  Proof.
    split; auto.
  Qed.

  (* An RAMixin is a structure which combines all the parts of an RA into one
     Coq structure, together with all the properties that the operations and
     functions satisfy. *)
  Definition mcounterRA_mixin : RAMixin mcounterRAT.
  Proof.
    split; try apply _; try done.
    - unfold valid, op, mcounterRAop, mcounterRAValid. intros ? ? cx -> ?; exists cx. done.
    (* The operation is associative. *)
    - unfold op, mcounterRAop. intros [[]] [[]] [[]]; rewrite !Nat.max_assoc; reflexivity.
    (* The operation is commutative. *)
    - unfold op, mcounterRAop. intros [[]] [[]]; rewrite Nat.max_comm; reflexivity.
    (* Core axioms. *)
    - unfold pcore, mcounterRACore, op, mcounterRAop; intros [[]] [[]] [=->]; rewrite Nat.max_idempotent; auto.
    - unfold pcore, mcounterRACore, op, mcounterRAop; intros [[]] [[]] [=->]; auto.
    - unfold pcore, mcounterRACore, op, mcounterRAop. 
      intros [x n] [y m] cx Hleq%mcounterRA_included_aux [=<-].
      exists (MCounter Bot m); split; first auto.
      by apply mcounterRA_included_frag.
    - (* Validity axiom: validity is down-closed with respect to the extension order. *)
      intros [[]].
      + reflexivity.
      + unfold op, mcounterRAop; intros [[]] [].
      + unfold op, mcounterRAop; intros [[]].
        * rewrite !mcounterRA_valid. eauto with arith.
        * intros [].
        * intros [].
  Qed.

  (* We finally wrap the type and the above mixin and make the structure
  available for typeclass search. The discreteR is a wrapper for when our CMRA is
  "discrete" as described above. *)
  Canonical Structure mcounterRA := discreteR mcounterRAT mcounterRA_mixin.

  (* Some tactics and lemmas only apply for discrete CMRAs (what we called RAs).
     To be able to use these we need to register our CMRA as a discrete one, to
     make this information available to typeclass search. *) 
  Local Instance mcounterRA_cmra_discrete : CmraDiscrete mcounterRA.
  Proof. apply discrete_cmra_discrete. Qed.

  (* A total CMRA (or RA) is the one where the core operation is a total
     function, i.e., the core of every element is defined. Some properties and
     lemmas only apply for such CMRAs, and so we register the fact that our CMRA
     is of this form.
   *)
  Local Instance mcounterRA_cmra_total : CmraTotal mcounterRA.
  Proof. intros [[]]; eauto. Qed.

  (* We define some abbreviation. We only define it as notation in this section
     since the same notation is already defined for the general authoritative RA
     construction in the Iris Coq library. 
   *)
  Local Notation "◯ n" := (MCounter Bot n%nat) (at level 20).
  Local Notation "● m" := (MCounter (NBT_incl m%nat) 0%nat) (at level 20).

  (* We now prove the three properties we claim were required from the resource
     algebra in Section 7.7. 
   *)
  (* CoreId x states that the core of x is x, which is one of the properties we claimed for the
     fragments. CoreId is a typeclass. *)
  Local Instance mcounterRA_frag_core (n : nat): CoreId (◯ n).
  Proof.
    rewrite /CoreId; reflexivity.
  Qed.

  Lemma mcounterRA_valid_auth_frag m n: ✓ (● m ⋅ ◯ n) ↔ (n ≤ m)%nat.
  Proof.
    apply mcounterRA_valid.
  Qed.

  Lemma mcounterRA_update m n: ((● m ⋅ ◯ n) : mcounterRA) ~~> (● (1 + m) ⋅ ◯ (1 + n)).
  Proof.
    (* Use the specialized definition of update, since our RA is a nice one. *)
    apply cmra_discrete_update.
    intros [[] k].
    - rewrite /op /cmra_op !mcounterRA_valid; lia.
    - intros [].
    - intros [].
  Qed.

  (* We now need to tell Coq to use our RA as one of the RA's in the instantiation of Iris. *)
  (* This is achieved via the subG constructor. All of this is boilerplate, so
     the proofs are trivial, with the tactics provided by the library. *)
  Class mcounterG Σ := MCounterG { mcounter_inG :: inG Σ mcounterRA }.
  Definition mcounterΣ : gFunctors := #[GFunctor mcounterRA].
  
  Global Instance subG_mcounterΣ {Σ} : subG mcounterΣ Σ → mcounterG Σ.
  Proof. solve_inG. Qed.

  (* We can now verify the programs. *)
  (* We start off as in the previous example, with some boilerplate code. *)
  Context `{!heapGS Σ, !mcounterG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* The counter invariant as defined in the notes. The only difference is that
     we are using the namespace N for the invariant, instead of existentially
     quantifying the invariant name. *)
  Definition counter_inv (ℓ : loc) (γ : gname) : iProp := (∃ (m : nat), ℓ ↦ #m ∗ own γ (● m))%I.

  (* the isCounter predicate as in the notes. *)
  Definition isCounter (ℓ : loc) (n : nat) : iProp :=
    (∃ γ, own γ (◯ n) ∗ inv N (counter_inv ℓ γ))%I.

  (* isCounter is a persistent predicate. This is needed so we can share it among threads. *)
  (* We first need an auxiliary lemma, which tells Coq that ownership of fragments is persistent.
     This follows from the persistently-core axiom of the logic.
     Instead of proving this as a lemma we make it an instance of the Persistent class.
     This way Coq will be able to infer automatically whenever it needs the fact
     that ownership of fragments is persistent.
   *)
  Local Instance ownFrac_persistent γ n: Persistent (own γ (◯ n)).
  Proof.
   apply own_core_persistent, _.
  Qed.

  (* Now the proof of the main counter predicate is simple: Coq's typeclass
     search can automatically deduce that isCounter is persistent. It knows the
     closure properties of persistent propositions, e.g., existential
     quantification over a persistent predicate is persistent, and it knows that
     invariants are persistent. The final part it needs is that own γ (◯ n) is
     persistent, and we have just taught it that in the preceding lemma. *)
  Global Instance isCounter_persistent ℓ n: Persistent (isCounter ℓ n).
  Proof.
    apply _.
  Qed.

  (* We can now perform the main proofs. They are not very different from the
     proofs we have done previously. *) 
  Lemma newCounter_spec: {{{ True }}} newCounter #() {{{ v, RET #v; isCounter v 0 }}}.
  Proof.
    iIntros (Φ) "_ HCont".
    rewrite /newCounter.
    wp_lam.
    (* We allocate ghost state using the rule/lemma own_alloc. Since the
       conclusion of the rule is under a modality we wrap the application of
       this lemma with the call to the iMod tactic, which takes care of the
       bookkeeping, using the primitive rules of the modality. 
       In this case the tactic knows that |==> WP ... implies WP ... and thus removes it from the goal.
     *)
    iMod (own_alloc (● 0 ⋅ ◯ 0)) as (γ) "[HAuth HFrac]".
    - apply mcounterRA_valid_auth_frag; auto. (* NOTE: We use the validity property of the RA we have constructed. *)
    - wp_alloc ℓ as "Hpt".
      (* We now allocate an invariant. *)
      iMod (inv_alloc N _ (counter_inv ℓ γ) with "[Hpt HAuth]") as "HInv".
      + iExists 0%nat; iFrame.
      + iApply ("HCont" with "[HFrac HInv]").
        iExists γ; iFrame.
  Qed.
  
  (* The read method specification. *)
  Lemma read_spec ℓ n: {{{ isCounter ℓ n }}} read #ℓ {{{ m, RET #m; ⌜n ≤ m⌝%nat }}}.
  Proof.
    iIntros (Φ) "HCounter HCont".
    iDestruct "HCounter" as (γ) "[HOwnFrag HInv]".
    rewrite /read.
    wp_lam.
    iInv N as (m) ">[Hpt HOwnAuth]" "HClose".
    wp_load.
    (* NOTE: We use the validity property of the RA we have constructed. From the fact that we own 
             ◯ n and ● m to conclude that n ≤ m. *)
    iCombine "HOwnAuth HOwnFrag" gives %H%mcounterRA_valid_auth_frag. 
    iMod ("HClose" with "[Hpt HOwnAuth]") as "_".
    { iNext; iExists m; iFrame. }
    iModIntro.
    iApply "HCont"; done.
  Qed.

  (* The read method specification. *)
  Lemma incr_spec ℓ n: {{{ isCounter ℓ n }}} incr #ℓ {{{ RET #(); isCounter ℓ (1 + n)%nat }}}.
  Proof.
    iIntros (Φ) "HCounter HCont".
    iDestruct "HCounter" as (γ) "[HOwnFrag #HInv]".
    iLöb as "IH".
    rewrite /incr.
    wp_lam.
    wp_bind (! _)%E.
    iInv N as (m) ">[Hpt HOwnAuth]" "HClose".
    wp_load.
    iCombine "HOwnAuth HOwnFrag" gives %H%mcounterRA_valid_auth_frag.
    iMod ("HClose" with "[Hpt HOwnAuth]") as "_".
    { iNext; iExists m; iFrame. }
    iModIntro.
    wp_let; wp_op; wp_let.
    wp_bind (CmpXchg _ _ _)%E.
    iInv N as (k) ">[Hpt HOwnAuth]" "HClose".
    destruct (decide (k = m)); subst.
    + wp_cmpxchg_suc.
      (* If the CAS succeeds we need to update our ghost state. This is achieved using the own_update rule/lemma.
         The arguments are the ghost name and the ghost resources x from which and to which we are updating.
         Finally we need to give up own γ x to get ownership of the new resources.
         We do this using the "with ..." syntax.
         Again, the conclusion of the update rule is under the update modality,
         and thus we wrap the application of the lemma with the iMod tactic. *)
      iMod (own_update γ ((● m ⋅ ◯ n) : mcounterRA) (● (1 + m) ⋅ ◯ (1 + n)) with "[HOwnFrag HOwnAuth]") as "[HOwnAuth HOwnFrag]".
      { apply mcounterRA_update. } (* We need the final property of the RA we proved above: the frame preserving update from (● m ⋅ ◯ n) to (● (1 + m) ⋅ ◯ (1 + n)). *)
      { rewrite own_op; iFrame. }
      iMod ("HClose" with "[Hpt HOwnAuth]") as "_".
      { iNext; iExists (1 + m)%nat.
        rewrite Nat2Z.inj_succ Z.add_1_l; iFrame. }
      iModIntro; wp_pures; iApply ("HCont" with "[HInv HOwnFrag]").
      iExists γ; iFrame "#"; iFrame.
    + wp_cmpxchg_fail; first intros ?; simplify_eq.
      iMod ("HClose" with "[Hpt HOwnAuth]") as "_".
      - iExists k; iFrame.
      - iModIntro. wp_proj. wp_if.
        iApply ("IH" with "HOwnFrag HCont"); iFrame.
  Qed.
End monotone_counter.

(* Finally, we make the [isCounter] predicate opaque to typeclass search, which
avoids expensive unfolding of abstract predicates in users of our specification.
*)
Global Typeclasses Opaque isCounter.

(* In the preceding section we spent a lot of time defining our own resource
   algebra and proving it satisfies all the needed properties. The same patterns
   appear often in proof development, and thus the iris Coq library provides
   several building blocks for constructing resource algebras.

   In the following section we repeat the above specification, but with a
   resource algebra constructed using these building blocks. We will see that
   this will save us quite a bit of work.

   As we stated in an exercise in the counter modules section of the lecture
   notes, the resource algebra we constructed above is nothing but Auth(N.max).
   Auth and N.max are both part of the iris Coq library. They are called authR
   and max_natUR (standing for authoritative Resource algebra and max nat Unital
   Resource algebra). *)

(* Auth is defined in iris.algebra.auth. *)
From iris.algebra Require Import auth.

(* The following section is a generic update property of the authoritative construction.
   In the Iris Coq library there are several update lemmas, using the concept of local updates
   (notation x ~l~> y, and the definition is called local_update).
   
   The two updates in the following section are the same as stated in the exercise in the notes.
*)
Section auth_update.
  Context {U : ucmra}.

  Lemma auth_update_add (x y z : U): ✓ (x ⋅ z) → ● x ⋅ ◯ y ~~> ● (x ⋅ z) ⋅ ◯ (y ⋅ z).
  Proof.
    intros ?.
    (* auth_update is the generic update rule for the auth RA. It reduces a
       frame preserving update to that of a local update. *)
    apply auth_update.
    intros ? mz ? Heq.
    split.
    - apply cmra_valid_validN; auto.
    - simpl in *.
      rewrite Heq.
      destruct mz; simpl; auto.
      rewrite -assoc (comm _ _ z) assoc //.
  Qed.

  Lemma auth_update_add' (x y z w : U): ✓ (x ⋅ z) → w ≼ z → ● x ⋅ ◯ y ~~> ● (x ⋅ z) ⋅ ◯ (y ⋅ w).
  Proof.
    (* The proof of this lemma uses the previous lemma, together with the fact
       that ~~> is transitive, and the fact that we always have the frame
       preserving update from a ⋅ b to a. This is proved in cmra_update_op_l in
       the Coq library.
    *)
    intros Hv [? He].
    etransitivity.
    { apply (auth_update_add x y z Hv). }
    rewrite {2}He assoc auth_frag_op assoc.
    apply cmra_update_op_l.
  Qed.
End auth_update.

Section monotone_counter'.
  (* We tell Coq that our Iris instantiation has the following resource
     algebras. Note that the only diffference from above is that we use authR
     max_natUR in place of the resource algebra mcounterRA we constructed above. *)
  Class mcounterG' Σ := MCounterG' { mcounter_inG' :: inG Σ (authR max_natUR)}.
  Definition mcounterΣ' : gFunctors := #[GFunctor (authR max_natUR)].

  Global Instance subG_mcounterΣ' {Σ} : subG mcounterΣ' Σ → mcounterG' Σ.
  Proof. solve_inG. Qed.

  (* We now prove the same three properties we claim were required from the resource
     algebra in Section 7.7.  *)
  Local Instance mcounterRA_frag_core' (n : max_natUR): CoreId (◯ n).
  Proof.
    apply _.
    (* CoreID is a typeclass, so typeclass search can automatically deduce what
       we want. Concretely, the proof follows by lemmas auth_frag_core_id and
       max_nat_core_id proved in the Iris Coq library.
       In fact, we would not even need this instance, typeclass search would
       deduce it automatically. *)
  Qed.

  Lemma mcounterRA_valid_auth_frag' (m n : max_natUR): ✓ (● m ⋅ ◯ n) ↔ (max_nat_car n ≤ max_nat_car m)%nat.
  Proof.
    (* Use a simplified definition of validity for when the underlying CMRA is discrete, i.e., an RA.
       The general definition also involves the use of step-indices, which is not needed in our case. *)
    rewrite auth_both_valid_discrete.
    split.
    - intros [? _]; by apply max_nat_included.
    - intros ?%max_nat_included; done.
  Qed.

  Lemma max_nat_op_succ m : MaxNat (S m) = MaxNat m ⋅ MaxNat (S m).
  Proof. rewrite max_nat_op. apply f_equal. lia. Qed.

  Lemma mcounterRA_update' (m n : max_natUR) :
    ● m ⋅ ◯ n ~~> ● MaxNat (S (max_nat_car m)) ⋅ ◯ MaxNat (S (max_nat_car n)).
  Proof.
    destruct m as [m], n as [n]. simpl.
    rewrite (max_nat_op_succ m) (max_nat_op_succ n).
    apply cmra_update_valid0. intros ?%cmra_discrete_valid%mcounterRA_valid_auth_frag'.
    simpl in *. apply auth_update_add'; first reflexivity.
    exists (MaxNat (S m)). rewrite max_nat_op. apply f_equal. lia.
  Qed.

  (* We can now verify the programs. *)
  (* We start off as in the previous example, with some boilerplate code. *)
  Context `{!heapGS Σ, !mcounterG' Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* The rest of this section is exactly the same as the preceding one. We use
     the properties of the RA we have proved above. *)
  Definition counter_inv' (ℓ : loc) (γ : gname) : iProp := (∃ (m : nat), ℓ ↦ #m ∗ own γ (● MaxNat m))%I.

  Definition isCounter' (ℓ : loc) (n : max_natUR) : iProp :=
    (∃ γ, own γ (◯ n) ∗ inv N (counter_inv' ℓ γ))%I.

  Global Instance isCounter_persistent' ℓ n: Persistent (isCounter' ℓ n).
  Proof.
    apply _.
  Qed.

  Lemma newCounter_spec': {{{ True }}} newCounter #() {{{ v, RET #v; isCounter' v (MaxNat 0) }}}.
  Proof.
    iIntros (Φ) "_ HCont".
    rewrite /newCounter.
    wp_lam.
    iMod (own_alloc (● MaxNat 0 ⋅ ◯ MaxNat 0)) as (γ) "[HAuth HFrac]".
    - apply mcounterRA_valid_auth_frag'; auto.
    - wp_alloc ℓ as "Hpt".
      iMod (inv_alloc N _ (counter_inv' ℓ γ) with "[Hpt HAuth]") as "HInv".
      + iExists 0%nat; iFrame.
      + iApply ("HCont" with "[HFrac HInv]").
        iExists γ; iFrame.
  Qed.

  (* The read method specification. *)
  Lemma read_spec' ℓ n : {{{ isCounter' ℓ (MaxNat n) }}} read #ℓ {{{ m, RET #m; ⌜n ≤ m⌝%nat }}}.
  Proof.
    iIntros (Φ) "HCounter HCont".
    iDestruct "HCounter" as (γ) "[HOwnFrag HInv]".
    rewrite /read.
    wp_lam.
    iInv N as (m) ">[Hpt HOwnAuth]" "HClose".
    wp_load.
    iCombine "HOwnAuth HOwnFrag" gives %H%mcounterRA_valid_auth_frag'.
    iMod ("HClose" with "[Hpt HOwnAuth]") as "_".
    { iNext; iExists m; iFrame. }
    iModIntro.
    iApply "HCont"; done.
  Qed.

  (* The read method specification. *)
  Lemma incr_spec' ℓ n : {{{ isCounter' ℓ (MaxNat n) }}} incr #ℓ {{{ RET #(); isCounter' ℓ (MaxNat (1 + n)) }}}.
  Proof.
    iIntros (Φ) "HCounter HCont".
    iDestruct "HCounter" as (γ) "[HOwnFrag #HInv]".
    iLöb as "IH".
    rewrite /incr.
    wp_lam.
    wp_bind (! _)%E.
    iInv N as (m) ">[Hpt HOwnAuth]" "HClose".
    wp_load.
    iCombine "HOwnAuth HOwnFrag" gives %H%mcounterRA_valid_auth_frag'.
    iMod ("HClose" with "[Hpt HOwnAuth]") as "_".
    { iNext; iExists m; iFrame. }
    iModIntro.
    wp_let; wp_op; wp_let.
    wp_bind (CmpXchg _ _ _)%E.
    iInv N as (k) ">[Hpt HOwnAuth]" "HClose".
    destruct (decide (k = m)); subst.
    + wp_cmpxchg_suc.
      iMod (own_update γ (● (MaxNat m) ⋅ ◯ (MaxNat n)) (● (MaxNat (S m)) ⋅ (◯ (MaxNat (S n)))) with "[HOwnFrag HOwnAuth]") as "[HOwnAuth HOwnFrag]".
      { apply mcounterRA_update'. }
      { rewrite own_op; iFrame. }
      iMod ("HClose" with "[Hpt HOwnAuth]") as "_".
      { iNext; iExists (1 + m)%nat.
        rewrite Nat2Z.inj_succ Z.add_1_l; iFrame. }
      iModIntro; wp_pures; iApply ("HCont" with "[HInv HOwnFrag]").
      iExists γ; iFrame "#"; iFrame.
    + wp_cmpxchg_fail; first intros ?; simplify_eq.
      iMod ("HClose" with "[Hpt HOwnAuth]") as "_".
      - iExists k; iFrame.
      - iModIntro. wp_proj. wp_if.
        iApply ("IH" with "HOwnFrag HCont"); iFrame.
  Qed.
End monotone_counter'.

(* Counter with contributions. *)
(* As a final example in this example file we give the more precise specification to the counter. *) 
(* As explained in the lecture notes we need a different resource algebra: the
   authoritative resource algebra on the product of the RA of fractions and the
   RA of natural numbers, with an added unit.

   The combination of the RA of fractions and the authoritative RA in this way
   is fairly common, and so the Iris Coq library provides frac_authR (CM)RA. *)

From iris.algebra Require Import frac_auth.

Section ccounter.
  (* We start as we did before, telling Coq what we assume from the Iris instantiation. *)
  (* Note that now we use natR as the underlying resource algebra. This is the
     RA of natural numbers with addition as the operation. *)
  Class ccounterG Σ := CCounterG { ccounter_inG :: inG Σ (frac_authR natR) }.
  Definition ccounterΣ : gFunctors := #[GFunctor (frac_authR natR)].

  Global Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
  Proof. solve_inG. Qed.


  (* The first thing we are going to prove are the properties of the resource
     algebra, specialized to our use case. These are listed in the exercise in
     the relevant section of the lecture notes. *)
  (* We are using some new notation. The frac_auth library defines the notation
     ◯F{q} n to mean ◯ (q, n) as we used in the lecture notes. Further, ●F m
     means ● (1, m) and ◯F n means ◯ (1, n). *)
  Lemma ccounterRA_valid (m n : natR) (q : frac): ✓ (●F m ⋅ ◯F{q} n) → (n ≤ m)%nat.
  Proof.
    intros ?.
    (* This property follows directly from the generic properties of the relevant RAs. *)
    apply nat_included. by apply: (frac_auth_included_total q).
  Qed.

  Lemma ccounterRA_valid_full (m n : natR): ✓ (●F m ⋅ ◯F n) → (n = m)%nat.
  Proof.
    by intros ?%frac_auth_agree.
  Qed.

  Lemma ccounterRA_update (m n : natR) (q : frac): (●F m ⋅ ◯F{q} n) ~~> (●F (S m) ⋅ ◯F{q} (S n)).
  Proof.
    apply frac_auth_update, (nat_local_update _ _ (S _) (S _)).
    lia.
  Qed.

  (* We have all the properties of the RAs needed and thus we can proceed with
     the proof, which proceeds largely as before, modulo the changes in
     invariants.

     There is one important difference in the definition of is_ccounter. The
     ghost name γ is not hidden. This is because now is_ccounter is not
     persistent, and to share it we have the is_ccounter_op lemma, which would
     not hold if we were to existentially quantify γ as we did in the previous
     examples.
  *)
  Context `{!heapGS Σ, !ccounterG Σ} (N : namespace).

  Definition ccounter_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n, own γ (●F n) ∗ l ↦ #n)%I.

  Definition is_ccounter (γ : gname) (l : loc) (q : frac) (n : natR) : iProp Σ :=
    (own γ (◯F{q} n) ∗ inv N (ccounter_inv γ l))%I.

  (** The main proofs. *)

  (* As explained in the notes the is_ccounter predicate for this specificatin is not persistent.
     However it is still shareable in the following restricted way.
   *)
  Lemma is_ccounter_op γ ℓ q1 q2 (n1 n2 : nat) :
    is_ccounter γ ℓ (q1 + q2) (n1 + n2)%nat ⊣⊢ is_ccounter γ ℓ q1 n1 ∗ is_ccounter γ ℓ q2 n2.
  Proof.
    apply bi.equiv_entails; split; rewrite /is_ccounter frac_auth_frag_op own_op.
    - iIntros "[? #?]".
      iFrame "#"; iFrame.
    - iIntros "[[? #?] [? _]]".
      iFrame "#"; iFrame.
  Qed.

  Lemma newcounter_contrib_spec (R : iProp Σ) :
    {{{ True }}}
        newCounter #()
    {{{ γ ℓ, RET #ℓ; is_ccounter γ ℓ 1 0%nat }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /newCounter /=. wp_lam. wp_alloc ℓ as "Hpt".
    iMod (own_alloc (●F O%nat ⋅ ◯F 0%nat)) as (γ) "[Hγ Hγ']"; first by apply auth_both_valid_discrete.
    iMod (inv_alloc N _ (ccounter_inv γ ℓ) with "[Hpt Hγ]").
    { iNext. iExists 0%nat. by iFrame. }
    iModIntro. iApply "HΦ". rewrite /is_ccounter; eauto.
  Qed.

  Lemma incr_contrib_spec γ ℓ q n :
    {{{ is_ccounter γ ℓ q n  }}}
        incr #ℓ
    {{{ RET #(); is_ccounter γ ℓ q (S n) }}}.
  Proof.
    iIntros (Φ) "[Hown #Hinv] HΦ". iLöb as "IH". wp_rec.
    wp_bind (! _)%E. iInv N as (c) ">[Hγ Hpt]" "Hclose".
    wp_load. iMod ("Hclose" with "[Hpt Hγ]") as "_"; [iNext; iExists c; by iFrame|].
    iModIntro. wp_let. wp_op. wp_let.
    wp_bind (CmpXchg _ _ _). iInv N as (c') ">[Hγ Hpt]" "Hclose".
    destruct (decide (c' = c)) as [->|].
    - iMod (own_update_2 with "Hγ Hown") as "[Hγ Hown]".
      { apply ccounterRA_update. } (* We use the update lemma for our RA. *)
      wp_cmpxchg_suc. iMod ("Hclose" with "[Hpt Hγ]") as "_".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      iModIntro. wp_pures. iApply "HΦ". by iFrame "Hinv".
    - wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]).
      iMod ("Hclose" with "[Hpt Hγ]") as "_"; [iNext; iExists c'; by iFrame|].
      iModIntro. wp_pures. by iApply ("IH" with "[Hown] [HΦ]"); auto.
  Qed.

  Lemma read_contrib_spec γ ℓ q n :
    {{{ is_ccounter γ ℓ q n }}}
        read #ℓ
    {{{ c, RET #c; ⌜n ≤ c⌝%nat ∧ is_ccounter γ ℓ q n }}}.
  Proof.
    iIntros (Φ) "[Hown #Hinv] HΦ".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hpt]" "Hclose". wp_load.
    iCombine "Hγ Hown" gives % ?%ccounterRA_valid. (* We use the validity property of our RA. *)
    iMod ("Hclose" with "[Hpt Hγ]") as "_"; [iNext; iExists c; by iFrame|].
    iApply ("HΦ" with "[-]"); rewrite /is_ccounter; eauto.
  Qed.

  Lemma read_contrib_spec_1 γ ℓ n :
    {{{ is_ccounter γ ℓ 1 n }}} read #ℓ
    {{{ m, RET #m; ⌜m = n⌝ ∗ is_ccounter γ ℓ 1 m }}}.
  Proof.
    iIntros (Φ) "[Hown #Hinv] HΦ".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hpt]" "Hclose". wp_load.
    iCombine "Hγ Hown" gives % <-%ccounterRA_valid_full. (* We use the validity property of our RA. *)
    iMod ("Hclose" with "[Hpt Hγ]") as "_"; [iNext; iExists n; by iFrame|].
    iApply "HΦ"; iModIntro. iFrame "Hown #"; done.
  Qed.
End ccounter.
