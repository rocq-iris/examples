(* In this file we explain how to do the stack example from Section 4.3 of
   the Iris Lecture Notes *)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.


(*  ---------------------------------------------------------------------- *)

Section stack_code.
  (* This section contains the code of the stack functions we specify *)

  Definition new_stack : val := λ: <>, ref NONEV.

  Definition push : val := λ: "s", λ: "x",
                           let: "hd" := !"s" in
                           let: "p" := ("x", "hd") in
                           "s" <- SOME (ref "p").

  Definition pop : val := (λ: "s",
                           let: "hd" := !"s" in
                           match: "hd" with
                             NONE => NONE
                           | SOME "l" =>
                             let: "p" := !"l" in
                             let: "x" := Fst "p" in
                             "s" <- Snd "p" ;; SOME "x"
                           end).
End stack_code.

(*  ---------------------------------------------------------------------- *)

Section stack_model.

  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types ℓ : loc.
  (* Here is the basic is_stack representation predicate.
     A stack is a pointer to the head of a linked list.
     Thus we first specify what a linked list is. One option is the following.
   *)
  Fixpoint is_list (hd : val) (xs : list val) : iProp :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ ℓ hd', ⌜hd = SOMEV #ℓ⌝ ∗ ℓ ↦ (x,hd') ∗ is_list hd' xs
  end%I.

  Definition is_stack (s : val) (xs : list val): iProp :=
    (∃ (ℓ : loc) (hd : val), ⌜s = #ℓ⌝ ∗ ℓ ↦ hd ∗ is_list hd xs)%I.
End stack_model.


(*  ---------------------------------------------------------------------- *)
Section stack_spec.
  (* This section contains the specifications and proofs for the stack functions.
     The specifications and proofs are explained in the Iris Lecture Notes
   *)
  Context `{!heapGS Σ}.

  Lemma new_stack_spec:
    {{{ True }}}
      new_stack #()
      {{{ s, RET s; is_stack s [] }}}.
  Proof.
    iIntros (ϕ) "_ HΦ".
    wp_lam.
    wp_alloc ℓ as "Hpt".
    iApply "HΦ".
    iExists ℓ, NONEV.
    iFrame; done.
  Qed.

  Lemma push_spec s xs (x : val):
    {{{ is_stack s xs }}}
      push s x
      {{{ RET #(); is_stack s (x :: xs) }}}.
  Proof.
    iIntros (ϕ) "Hstack HΦ".
    iDestruct "Hstack" as (ℓ hd ->) "[Hpt Hlist]".
    wp_lam. wp_let.
    wp_load.
    wp_let.
    wp_pair.
    wp_let.
    wp_alloc ℓ' as "Hptℓ'".
    wp_store.
    iApply "HΦ".
    iExists ℓ, (SOMEV #ℓ'); iFrame.
    iSplitR; done.
  Qed.

  Lemma pop_spec_nonempty s (x : val) xs:
    {{{ is_stack s (x :: xs) }}}
      pop s
      {{{ RET (SOMEV x); is_stack s xs }}}.
  Proof.
    iIntros (ϕ) "Hstack HΦ".
    iDestruct "Hstack" as (ℓ hd ->) "[Hpt Hlist]".
    iDestruct "Hlist" as (ℓ' hd' ->) "[Hptℓ' Hlist]".
    wp_lam.
    wp_load.
    wp_let.
    wp_match.
    wp_load.
    wp_let.
    wp_proj.
    wp_let.
    wp_proj.
    wp_store.
    wp_pures.
    iApply "HΦ".
    iExists ℓ, hd'; by iFrame.
  Qed.

  Lemma pop_spec_empty s:
    {{{ is_stack s [] }}}
      pop s
      {{{ RET NONEV; is_stack s [] }}}.
  Proof.
    iIntros (ϕ) "Hstack HΦ".
    iDestruct "Hstack" as (ℓ hd ->) "[Hpt %]"; subst.
    wp_lam.
    wp_load.
    wp_pures.
    iApply "HΦ".
    iExists ℓ, NONEV; by iFrame.
  Qed.

End stack_spec.

Section stack_model_ownership.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types ℓ : loc.
  (* Here is the basic is_stack representation predicate.
     A stack is a pointer to the head of a linked list.
     Thus we first specify what a linked list is. One option is the following.
   *)
  Fixpoint is_list_own (hd : val) (Φs : list (val → iProp)) : iProp :=
    match Φs with
    | [] => ⌜hd = NONEV⌝
    | Φ :: Φs => ∃ ℓ x hd', ⌜hd = SOMEV #ℓ⌝ ∗ ℓ ↦ (x,hd') ∗ Φ x ∗ is_list_own hd' Φs
  end%I.

  Definition is_stack_own (s : val) (Φs : list (val → iProp)): iProp :=
    (∃ (ℓ : loc) (hd : val), ⌜s = #ℓ⌝ ∗ ℓ ↦ hd ∗ is_list_own hd Φs)%I.
End stack_model_ownership.

(*  ---------------------------------------------------------------------- *)
Section stack_ownership_spec.
  (* This section contains the specifications and proofs for the stack functions.
     The specifications and proofs are explained in the Iris Lecture Notes
   *)
  Context `{!heapGS Σ}.

Lemma newstack_ownership_spec:
  {{{ True }}}
    new_stack #()
  {{{ s, RET s; is_stack s [] }}}.
Proof.
  iIntros (ϕ) "_ HΦ".
  wp_lam.
  wp_alloc ℓ as "Hpt".
  iApply "HΦ".
  iExists ℓ, NONEV.
  iFrame; done.
Qed.

Lemma push_ownership_spec s Φ Φs (x : val):
  {{{ is_stack_own s Φs ∗ Φ x }}}
    push s x
  {{{ RET #(); is_stack_own s (Φ :: Φs) }}}.
Proof.
  iIntros (Ψ) "[Hstack HΦx] HΨ".
  iDestruct "Hstack" as (ℓ hd ->) "[Hpt Hlist]".
  wp_lam; wp_let.
  wp_load.
  wp_alloc ℓ' as "Hptℓ'".
  wp_store.
  iApply "HΨ".
  iExists ℓ, (SOMEV #ℓ'); iFrame.
  iSplitR; done.
Qed.

Lemma pop_ownership_spec_nonempty s Φ Φs:
  {{{ is_stack_own s (Φ :: Φs) }}}
    pop s
  {{{x, RET (SOMEV x); Φ x ∗ is_stack_own s Φs }}}.
Proof.
  iIntros (Ψ) "Hstack HΨ".
  iDestruct "Hstack" as (ℓ hd ->) "[Hpt Hlist]".
  iDestruct "Hlist" as (ℓ' x hd' ->) "[Hptℓ' [HΦ Hlist]]".
  wp_lam.
  wp_load.
  wp_let.
  wp_match.
  wp_load.
  wp_let.
  wp_proj.
  wp_let.
  wp_proj.
  wp_store.
  wp_inj.
  iApply "HΨ".
  iFrame "HΦ".
  iExists ℓ, hd'; by iFrame.
Qed.

Lemma pop_ownership_spec_empty s:
  {{{ is_stack s [] }}}
    pop s
  {{{ RET NONEV; is_stack s [] }}}.
Proof.
  iIntros (ϕ) "Hstack HΦ".
  iDestruct "Hstack" as (ℓ hd ->) "[Hpt %]"; subst.
  wp_lam.
  wp_load.
  wp_pures.
  iApply "HΦ".
  iExists ℓ, NONEV; by iFrame.
Qed.

End stack_ownership_spec.

(* Exercise 1: Derive the other specifications from the lecture notes.
   Exercise 2: Derive the first specification from the second. That is, from is_stack_own define is_stack, and reprove all the methods in section stack_spec from the specifications in stack_ownership_spec.
 *)
