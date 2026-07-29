(* This file contains the case study on recursion-through-the-store which
   is described in the Iris Lecture Notes in the case study section on Invariants
   for Sequential Programs.
 *)

(* Definition of invariants and their rules (expressed using the fancy update
   modality). *)
From iris.base_logic.lib Require Export invariants.

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

(* The following line imports some Coq configuration we commonly use in Iris
   projects, mostly with the goal of catching common mistakes. *)

Section recursion_through_the_store.

(* In order to do the proof we need to assume certain things about the
   instantiation of Iris. The particular, even the heap is handled in an
   analogous way as other ghost state. This line states that we assume the
   Iris instantiation has sufficient structure to manipulate the heap, e.g.,
   it allows us to use the points-to predicate. *)

Context `{!heapGS Σ}.
Implicit Types l : loc.


(* This is the code for the recursion through the store operator *)
Definition myrec : val :=
  λ: "f",
  let: "r" := ref(λ: "x", "x" ) in
  "r" <- (λ: "x", "f" (!"r") "x");;
          !"r".

(* Here is the specification for the recursion through the store function.
   See the Iris Lecture Notes for an in-depth discussion of both the specification and
   the proof. *)
Lemma myrec_spec (P: val -> iProp Σ) (Q: val -> val -> iProp Σ) (F v1: val) :
  {{{
       ( ∀f : val,  ∀v2:val, {{{(∀ v3 :val, {{{P v3 }}} f v3 {{{u, RET u; Q u v3 }}})
                                ∗ P v2 }}}
            F f v2
            {{{u, RET u; Q u v2}}})
            ∗ P v1
  }}}
myrec F v1
  {{{u, RET u; Q u v1}}}.
Proof.
   iIntros (ϕ) "[#H P] Q".
   wp_lam.
   wp_alloc r as "r".
   wp_let.
   wp_store.
   wp_load.
   iMod (inv_alloc (nroot.@"myrec") _ _ with "[r]") as "#inv"; first by iNext; iExact "r".
   iAssert (▷ ∀ u : val, Q u v1 -∗ ϕ u)%I with "[Q]" as "Q"; first done.
   iLöb as "IH" forall(v1 ϕ).
   wp_lam.
   wp_bind (! _)%E.
   iInv (nroot.@"myrec") as "r" "cl".
   wp_load.
   iMod ("cl" with "[r]") as "_"; first done. iModIntro.
   iApply ("H" with "[P]"); last done.
   iFrame. iIntros (v3).
   iModIntro. iIntros (Φ) "P Q". iApply ("IH" with "[P][Q]"); done.
Qed.

End recursion_through_the_store.

Section factorial_client.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.

  (* In this section we show how to specify and prove correctness of a
     factorial fucntion implemented using our recursion through the
     store function *)

  (* Here is the mathematical factorial function and a few properties
     related to that. *)
  Fixpoint factorial (n: nat) : nat:=
  match n with
    | O => 1
    | S n' => S n' * factorial n'
  end.

  Lemma factorial_spec_S (n : nat) : factorial (S n) = (S n) * factorial n.
  Proof.
    reflexivity.
  Qed.

  Definition fac_int (x : Z) := Z.of_nat (factorial (Z.to_nat x)).

  Lemma fac_int_eq_0: fac_int 0 = 1%Z.
  Proof.
    reflexivity.
  Qed.

  Lemma fac_int_eq (x : Z):
    (1 ≤ x)%Z → fac_int x = (fac_int (x - 1) * x)%Z.
  Proof.
    intros ?.
    rewrite Z.mul_comm.
    rewrite /fac_int.
    assert (Z.to_nat x = S (Z.to_nat (x - 1))) as Heq.
    { transitivity (Z.to_nat (1 + (x - 1))).
      - f_equal; lia.
      - rewrite Z2Nat.inj_add; first auto; lia.
    }
    rewrite Heq factorial_spec_S -Heq Nat2Z.inj_mul Z2Nat.id //; lia.
  Qed.

  (* Now, for the code of the implementation of factorial *)

  (* Here is code for a multiplication function, which we will use
     to implement factorial. *)
  Definition times : val :=
    rec: "times" "x" "y" :=
      if: "x" = #0 then #0 else "y" + "times" ("x" - #1) "y".

  Lemma times_spec_aux (m : Z):
    ∀ n Φ , ▷ Φ (# (n * m)) -∗ WP times #n #m {{ Φ }}.
  Proof.
    iLöb as "IH".
    iIntros (n Φ) "ret".
    wp_lam. wp_let.
    wp_binop.
    case_bool_decide; simplify_eq/=.
    - wp_if. iApply "ret".
    - wp_if.
      wp_bind (_ - _)%E.
      wp_binop.
      wp_bind ((times _) _).
      iApply "IH"; iNext.
      wp_binop; first
        by replace (m + ((n - 1) * m))%Z with (n * m)%Z by lia.
  Qed.

  Lemma times_spec (n m : Z):
    {{{True}}}
      times #n #m
      {{{v, RET v; ⌜v = # ( n * m)⌝  }}}.
  Proof.
    iIntros (Φ) "_ ret".
    iApply (times_spec_aux with "[ret]").
    iNext; iApply "ret".
      by iIntros "!%".
  Qed.


  (* Here is the implementation code for factorial, implemented using the recursion
   through the store function *)
  Definition myfac  :=
    myrec (λ: "f" ,
           λ: "n",
           if: "n"=#0
           then #1
           else  times ("f" ("n" - #1) )  "n")%E.


  (* Finally, here is the specification that our implementation of factorial
     really does implement the mathematical factorial function. *)
  Lemma myfac_spec (n: Z):
    (0 ≤ n)%Z →
    {{{ True }}}
      myfac #n
    {{{ v, RET v; ⌜v = #(fac_int n)⌝ }}}.
  Proof.
    iIntros (Hleq Φ) "_ ret"; simplify_eq. unfold myfac. wp_pures.
    iApply (myrec_spec (fun v => ⌜∃m' : Z, (0 ≤ m')%Z ∧ to_val v = Some #m'⌝%I)
                       (fun u => fun v => ⌜∃m' : Z, to_val v = Some #m' ∧ u = #(fac_int m')⌝%I)).
    - iSplit; last eauto. iIntros (f v). iModIntro. iIntros (Φ') "spec_f ret".
      wp_lam. wp_let. iDestruct "spec_f" as "[spec_f %H]".
      destruct H as [m' [Hleqm' Heq%of_to_val]]; simplify_eq.
      wp_binop.
      case_bool_decide; simplify_eq/=; wp_if.
      + iApply "ret". iPureIntro. exists 0; done.
      + assert (m' ≠ 0) by naive_solver.
        wp_binop. wp_bind (f _ )%E.
        iApply ("spec_f" $! (#(m'-1))).
        * iIntros "!%".
          exists (m'-1)%Z; split; first lia; last auto.
        * iNext. iIntros (u [x [Heq ->]]).
          iApply times_spec; first done.
          iNext; iIntros (u) "%"; subst; iApply "ret".
          iIntros "!%".
          exists m'.
          simpl in Heq; simplify_eq.
          split; first auto.
          rewrite -fac_int_eq; first auto; lia.
    - iNext. iIntros (u (?&[=]&->)); simplify_eq. by iApply "ret".
  Qed.

End factorial_client.
