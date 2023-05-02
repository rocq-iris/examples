(* This file implements the "S-F" transition system resource algebra from example 8.16.
   Note that usually this resource algebra would be defined using existing abstractions,
   for example via "csumR (exclR unitO) unitR". For demonstration purposes, here it is
   defined from scratch.
 *)

From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import frac.
From iris.prelude Require Import options.

Section RADefinitions.

Inductive SF :=
    | S (* The starting state *)
    | F (* The final state *)
    | B. (* The invalid element "bottom" *)

Canonical Structure SFRAC := leibnizO SF.


Global Instance SFRAop : Op SF :=
  λ x y, match x, y with
           | F, F => F
           | _, _ => B end.

Global Instance SFRAValid : Valid SF :=
  λ x, match x with
       | S | F => True
       | _ => False end.

Global Instance SFRACore : PCore SF :=
  λ _, None.

(* Produce cameras from the RA *)
Definition SFRA_mixin : RAMixin SF.
Proof.
    split; try apply _; try done.
    (* The operation is associative. *)
    - unfold op, SFRAop. intros [] [] []; reflexivity.
    (* The operation is commutative. *)
    - unfold op, SFRAop. intros [] []; reflexivity.
    - (* Validity axiom: validity is down-closed with respect to the extension order. *)
      intros [] []; intros H; try (inversion H); auto.
Qed.

Canonical Structure SFRA := discreteR SF SFRA_mixin.

Global Instance SFRA_cmra_discrete : CmraDiscrete SFRA.
Proof. apply discrete_cmra_discrete. Qed.

Global Instance SFRA_S_exclusive : Exclusive S.
Proof. intros x. done. Qed.

(* States the duplicability of F. Alternatively can use "replace".
   NOTE: Usually would make F a core element of the resource algebra, which would make it persistent
   and thereby duplicable *)
Lemma SFRA_FF: F = F ⋅ F.
Proof.
  done.
Qed.

Lemma SFRA_update : (S : SF) ~~> F.
Proof.
  apply cmra_update_exclusive.
  done.
  (* *** Manual proof *** *)
  (* unfold "~~>". *)
  (* intros n mx. *)
  (* destruct mx as [x |]. *)
  (* - destruct x; contradiction. *)
  (* - done. *)
Qed.

Class SFG Σ := SF_G :: inG Σ (SFRA).
Class FracG Σ := Frac_G :: inG Σ (fracR).

End RADefinitions.


(* This section defines some basic lemmas that make using the resource algebras more practical. *)
Section RALemmas.
  Context (N : namespace).
  Context `{!SFG Σ}.
  Context `{!FracG Σ}.

Lemma own_frac_valid γ (x : Qp): own γ x ⊢ ⌜(x ≤ 1)%Qp⌝.
Proof.
  rewrite own_valid.
  iIntros "!%".
  apply frac_valid.
Qed.

Lemma own_SFRA_FF (γ: gname): own γ F ⊣⊢ own γ F ∗ own γ F.
Proof.
  apply (own_op _ F F).
  (* Alternative proof using lemmas from above *)
  (* rewrite -own_op. *)
  (* rewrite -SFRA_FF. *)
  (* reflexivity. *)
Qed.

(* This lemma states the incompatibility of S and F *)
Lemma own_SF_false (γ: gname): own γ S ∗ own γ F ⊢ False.
Proof.
  rewrite -own_op.
  rewrite own_valid.
  iIntros (Contra).
  contradiction.
Qed.

End RALemmas.
