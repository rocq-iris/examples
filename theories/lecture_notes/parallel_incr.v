(* In this file we explain how to do the "parallel increment" example using ghost state (Example
   8.31) from the lecture notes in Iris in Coq.

   That is, we want to specify that a non-atomic increment of a location by two threads
   results in the location being incremented by either 1 or 2.

   We assume that the reader has experimented with coq_intro_example_1.v, and
   thus we do not explain the features we have already explained there.
 *)

From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.heap_lang.lib Require Import par.
From iris.prelude Require Import options.

(* In the file sfra.v, the "S-F" transition system resource algebra from example 8.16 is implemented,
   along with some lemmas that will be useful here.
   It is mainly a technicality and not necessary to look at to understand the proof.
   An example on how to construct resource algebras can be found in coq_intro_example_2.v.
 *)
From iris_examples.lecture_notes Require Import sfra.

(* Definition of the program *)
Definition incr (ℓ : loc) : expr := #ℓ <- !#ℓ + #1.

Section proof.
  Context `{!heapGS Σ}.
  Context `{!spawnG Σ}.
  Notation iProp := (iProp Σ).
  Context (N : namespace).
  (* We have to add the resource algebra classes to the context *)
  Context `{!SFG Σ}.
  Context `{!FracG Σ}.

(* Proof idea

   To get a specification which precisely reflects the possible outcomes of the parallel increment,
   we use ghost state in an invariant to represent the possible states during an execution.
   The ghost state consists of two parts from two different resource algebras which we use in parallel:
   - A transition system (resource algebra SF) with the tokens S and F, where S can be updated to F, F is duplicable,
     and everything else except F⋅F is incompatible
   - 1/2 fractions, which can be combined into 1

   The transition system is used to keep track of whether we are in the starting state (S),
   which cannot exist at the end of execution, or one of the two final states (F), which are possible
   at the end of execution. However, to be able to state that the location will be incremented by
   exactly 1 or 2 after execution of the program (instead of "at least by one"), we also
   have to keep track of how many times the value has been logically incremented.
   To this end, we use two 1/2 fractions, which, owned by the threads, initially represent the ability to increment,
   and when given to the invariant, they represent the number of contributions of "+1" to the value at location ℓ.

   The invariant thus consists of three disjuncts:
   - the starting state, where ℓ points to n, represented by the ownership of the S token
   - the first final state, where ℓ points to n+1, represented by the ownership of an F token
     and a 1/2 token, which stands for one contribution of 1 to the value at ℓ
   - the second final state, where ℓ points to n+2, represented by the ownership of an F token
     and two 1/2 tokens, that is, a 1 token, which stands for two contributions of 1 to the value at ℓ
*)

Definition incr_inv (ℓ : loc) (γ1 γ2 : gname) (n : Z) : iProp :=
    ℓ ↦ #n ∗ own γ1 S
  ∨ ℓ ↦ #(n+1) ∗ own γ1 F ∗ own γ2 (1/2)%Qp
  ∨ ℓ ↦ #(n+2) ∗ own γ1 F ∗ own γ2 1%Qp.

(* Overview of the proof
   The proof starts with allocating ghost state: S from the SF resource algebra, and 1 from the fractional resource
   algebra. We are then able to allocate the invariant in the first state, using the fact that ℓ points to n
   at the beginning and that we own the S token.
   From this point on, we can proceed separately in each thread. Here we will make use of the two 1/2 fractions
   we own, passing one to each thread. This means that each thread has the possibility to contribute +1 to the
   value stored at location ℓ.
   As both threads are the same, we can extract a specification for the code of a single thread and
   then use it to prove our actual specification. As the location ℓ to be modified is governed
   by an invariant, it can be used by both threads simultaneously without having to think of
   interleavings in the proof. This nicely demonstrates the modularity of the logic, allowing us to verify parallel
   components separately.

   Each thread is then verified by receiving the invariant and a 1/2 token as resources.
   To read the current value from the location and to write the updated value back, we need to open the invariant.
   As the invariant can only be opened for an atomic step, it has to be opened and closed twice, once for
   reading and once for writing. Each time, we have to consider all possible states the invariant can be in
   and then have to show that one of the cases holds when closing it. Depending on where we are in the program
   (reading the value or storing the updated value) only some of the cases will be possible. The impossible
   cases will be ruled out using the definition of the resource algebras, namely by obtaining invalid
   elements, resulting in a precondition being False.
*)

(* The main part of the proof is showing a specification that holds for each
   of the threads. We start by proving this in a separate lemma. *)
Lemma incr_spec (ℓ : loc) (n : Z) (γ1 γ2 : gname):
  {{{ inv N (incr_inv ℓ γ1 γ2 n) ∗ own γ2 (1 / 2)%Qp }}}
    incr ℓ
  {{{ v, RET #v; own γ1 F }}}.
Proof.
  iIntros (Φ) "[#Inv Own1/2] Post".
  unfold incr.
  (* To prove that the increment results in an F token, we have to prove two triples,
     one for reading the value currently stored at ℓ, and then one for storing the
     incremented value. To prove each triple, we have to open the invariant to get access to ℓ, and
     then close it again after the one atomic step. *)
  wp_bind (!#ℓ)%E.
  (* In the first triple, we want to show that the value currently stored at ℓ is n or n+1,
     and that if it is n+1, the invariant is in a final state. This information we want to
     use as an assumption in the second triple. Thus we first use wp_wand to update the
     current postcondition accordingly. We have to use the 1/2 resource to prove the first
     triple, as we will need it to rule out the case where ℓ contains n+2. However, we will
     not consume this resource, so we restate the ownership in the postcondition. *)
  iApply ((wp_wand _ _ _ (fun v => (⌜v = #n⌝ ∨ ⌜v = #(n+1)⌝ ∗ own γ1 F) ∗ own γ2 (1 / 2)%Qp)%I) with "[Own1/2]").
  { (* The first triple about the result of !ℓ *)
    (* We now open the invariant and destruct it into its three cases, one for each of the states.
       In each case, we close the invariant again with the same resources we got from opening it. *)
    iInv N as ">[I | [I | I]]" "Iclose".
    - (* Case 1: ℓ ↦ #n ∗ own γ1 S *)
      iDestruct "I" as "(Hℓ & OwnS)".
      wp_load.
      (* To close the invariant in the same state, we provide the two resources again
         and use them to show the disjunct corresponding to that state. *)
      iMod ("Iclose" with "[Hℓ OwnS]") as "_".
      { iLeft. iFrame. }
      iFrame. iLeft. done.
    - (* Case 2: ℓ ↦ #(n + 1) ∗ own γ1 F ∗ own γ2 (1 / 2)%Qp *)
      (* This is analogous to the first case. *)
      iDestruct "I" as "(Hℓ & OwnF & Own1/2_I)".
      (* We have to duplicate F, to have one to close the invariant and one for the postcondition. *)
      iDestruct (own_SFRA_FF with "OwnF") as "[OwnF_1 OwnF_2]".
      wp_load.
      iMod ("Iclose" with "[Hℓ OwnF_1 Own1/2_I]") as "_".
      { iRight. iLeft. iFrame. }
      iFrame. iRight. iFrame. done.
    - (* Case 3: ℓ ↦ #(n + 2) ∗ own γ1 F ∗ own γ2 1%Qp
         This state is impossible, as it means we have already incremented twice, represented by
         the ownership of 1. In this thread we have not come to writing to ℓ yet (represented by
         still owning 1/2, which we would lose when closing the invariant in a new state ),
         ℓ could thus have at most been updated once (by the other thread). We get the contradiction
         by combining the 1 from the invariant with the 1/2 of this thread into the invalid element (1 + 1/2). *)
      iDestruct "I" as "(Hℓ & OwnF & Own1)".
      iCombine "Own1 Own1/2" as "Own3/2".
      iDestruct (own_valid with "Own3/2") as "%Hinvalid".
      contradiction.
  }
  { (* The second triple about storing the incremented v *)
    iIntros (v) "[Hv Own1/2]".
    (* We consider the two cases for the value of v *)
    iDestruct "Hv" as "[-> | [-> OwnF]]";
      wp_binop;
      (* To store the updated value, we again have to open the invariant.
         As before, we have to consider the different possible states the invariant can be in.
         Note that the state can have changed since we closed the invariant after reading,
         due to the other thread updating the value.
         Together with the two possible values for v, we get 6 subgoals. *)
      iInv N as ">[I | [I | I]]" "Iclose";
      (* Again the third case of the invariant (ℓ ↦ #(n + 2) ∗ own γ1 F ∗ own γ2 1%Qp) is impossible,
         as we could not have updated ℓ twice yet. Thus we solve the two corresponding
         subgoals with the contradiction obtained by combining 1 and 1/2, as before. *)
      try (
          iDestruct "I" as "(Hℓ & OwnF_I & Own1)";
          iCombine "Own1 Own1/2" as "Own3/2";
          iDestruct (own_valid with "Own3/2") as "%Hinvalid";
          contradiction
        );
      (* In the remaining cases, we store the updated value, and close the invariant
         in the corresponding state, depending on whether we stored n+1 or n+2.
         To update the invariant's state, we have to transfer the 1/2 that was given
         to this thread into the invariant. *)
      iDestruct "I" as "[Hℓ Own]";
      wp_store;
      try (replace (n+1+1)%Z with (n+2)%Z by lia).
    - (* Storing (n + 1), invariant was in state S *)
      (* We have to show the second disjunct of the invariant to close it, which
         in addition to the 1/2 requires an F token.
         As the invariant was in the S state before, we have to update S to F. *)
      iMod (own_update _ _ F with "Own") as "OwnF"; first (apply SFRA_update).
      (* We then duplicate F, because we need to pass one F to the conclusion too. *)
      iDestruct (own_SFRA_FF with "OwnF") as "[OwnF_1 OwnF_2]".
      iMod ("Iclose" with "[Hℓ OwnF_1 Own1/2]") as "_".
      { iRight. iLeft. iFrame. }
      iApply ("Post" with "OwnF_2").
    - (* Storing (n + 1), invariant was in state F 1/2 *)
      (* Again, we have to show the second disjunct of the invariant to close it.
         However, the invariant was already in this state, so we don't have to use
         our 1/2 to make a state transition. This corresponds to the situation where the other
         thread has incremented the value from n to n+1 after we read n, but before we stored n+1.
         We still have to duplicate the F token though, to be able to remember that the
         invariant is in a final state. *)
      iDestruct "Own" as "[OwnF Own1/2_I]".
      iDestruct (own_SFRA_FF with "OwnF") as "[OwnF_1 OwnF_2]".
      iMod ("Iclose" with "[Hℓ OwnF_1 Own1/2_I]") as "_".
      { iRight. iLeft. iFrame. }
      iApply ("Post" with "OwnF_2").
    - (* Storing (n + 2), invariant was in state S *)
      (* This case is impossible: the invariant cannot be in the starting state S
         if we have read n+1, which means that the value had already been updated once.
         We get a contradiction by combining the S token with the F token we got for reading v=n+1. *)
      iDestruct (own_SF_false with "[$Own $OwnF]") as "HFalse".
      done.
    - (* Storing (n + 2), invariant was in state F 1/2 *)
      (* This case represents the situation where both threads have run sequentially, i.e.,
         the other thread has updated to n+1 before we read the value. Having stored n+2,
         we have to show the third disjunct of the invariant, which requires us to transfer
         an additional 1/2 to the invariant to obtain the required 1. *)
      iDestruct "Own" as "(OwnF_I & Own1/2_I)".
      iCombine "Own1/2 Own1/2_I" as "Own1".
      iMod ("Iclose" with "[Hℓ OwnF_I Own1]") as "_".
      { iRight. iRight. iFrame. }
      iApply ("Post" with "OwnF").
  }
Qed.

(* The actual specification for the whole program.
   Here we make use of the specification for a single thread we proved above. *)
Lemma parallel_incr_spec (ℓ : loc) (n : Z):
  {{{ ℓ ↦ #n }}} (incr ℓ) ||| (incr ℓ) ;; !#ℓ {{{v, RET #v; ⌜(v = n+1)%Z⌝ ∨ ⌜(v = n+2)%Z⌝ }}}.
Proof using Type* N.
  iIntros (Φ) "Hℓ Post".
  (* We start by allocating the start token S and the fraction 1. *)
  iMod (own_alloc S) as (γ1) "OwnS"; first done.
  iMod (own_alloc 1%Qp) as (γ2) "Own1"; first done.
  (* We allocate the invariant in the first state, where we have to provide an S token. *)
  iMod (inv_alloc N _ (incr_inv ℓ γ1 γ2 n) with "[Hℓ OwnS]") as "#Inv".
  { iLeft. iFrame. }
  (* We continue by focusing on the main part of the program, the parallel increment. *)
  wp_bind (_ ||| _)%E.
  (* For proving a conclusion for each thread, we want to pass a 1/2 fraction to each.
     Therefore we have to split the 1 we have into two halves.
     As frac is a fractional type, iDestruct can split the resource into two equal parts. *)
  - iDestruct "Own1" as "[Own1/2_1 Own1/2_2]".
    (* We now apply the par rule, passing one of the 1/2 to each thread.
       The arguments are the conclusions of the threads, which (according to our incr_spec)
       in both cases we choose to be the ownership of the F token. This will allow us to
       conclude that when the program terminates, the invariant must be in one of the F states
       (as S is incompatible with F). *)
    wp_smart_apply (wp_par (λ _ , own γ1 F)%I (λ _ , own γ1 F)%I with "[Own1/2_1] [Own1/2_2]").
    (* We can now for each thread apply our incr_spec specification. *)
    + iApply (incr_spec ℓ n γ1 γ2 with "[Inv Own1/2_1]"); first by iFrame.
      iNext. iIntros (_) "H". done.
    + iApply (incr_spec ℓ n γ1 γ2 with "[Inv Own1/2_2]"); first by iFrame.
      iNext. iIntros (_) "H". done.
    + (* As the final part, we have to show the second triple for reading the location,
         making use of the conclusions we get from both threads. *)
      iIntros (v1 v2) "OwnF".
      (* We get an F token from both threads, each stating that after the execution of one thread,
         the invariant must be in one of the final statse. *)
      iDestruct "OwnF" as "[OwnF _]".
      iNext.
      wp_pures.
      (* To read the location, we have to open the invariant again.
         We get three cases corresponding to the disjuncts in the invariant.
         As we have the F token, only the final states are possible cases, as we will see next.
         As we are only reading, as before we close the invariant again with the same resources
         we got from opening it. *)
      iInv N as ">[I | [I | I]]" "Iclose";
      iDestruct "I" as "[Hℓ Own]".
      * (* Case 1: ℓ ↦ #n, S
           This state is not possible as both threads either store n+1 or n+2 in ℓ.
           This is reflected by the incompatibility of owning the S token and an F token.
           To obtain a contradiction, we combine the S and F tokens as before. *)
        iDestruct (own_SF_false with "[$Own $OwnF]") as "HFalse".
        done.
      * (* Case 2: ℓ ↦ #(n + 1), F 1/2
           This state corresponds to the situation where only one thread
           has actually incremented the value. *)
        wp_load.
        (* As we only read the value stored at ℓ, we can close the invariant again
           with the same resources we got from opening. *)
        iMod ("Iclose" with "[Hℓ Own]") as "_".
        { iRight. iLeft. iFrame. }
        iModIntro. iApply "Post". iLeft. done.
      * (* Case 3: ℓ ↦ #(n + 2), F 1
           This state corresponds to the situation where both threads have
           incremented the value subsequently. *)
        wp_load.
        iMod ("Iclose" with "[Hℓ Own]") as "_".
        { iRight. iRight. iFrame. }
        iModIntro. iApply "Post". iRight. done.
Qed.

End proof.

(*  LocalWords:  disjuncts disjunct postcondition duplicable interleavings
(*  LocalWords:  modularity
 *)
 *)
