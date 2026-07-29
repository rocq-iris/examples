From iris.bi Require Export bi.
From iris_examples.cl_logic Require Export clprop.
From iris.prelude Require Import options.
Import clProp_primitive.

(** BI instances for [clProp], and re-stating the remaining primitive laws in
terms of the BI interface.  This file does *not* unseal. *)

(** We pick [*] and [-*] to coincide with [∧] and [→], respectively. This seems
to be the most reasonable choice to fit a "pure" higher-order logic into the
proofmode's BI framework. *)
Definition clProp_emp : clProp := clProp_pure True.
Definition clProp_sep : clProp → clProp → clProp := clProp_and.
Definition clProp_wand : clProp → clProp → clProp := clProp_impl.
Definition clProp_persistently (P : clProp) : clProp := P.
Definition clProp_later (P : clProp) : clProp := clProp_pure True.

Local Existing Instance entails_po.

Lemma clProp_bi_mixin :
  BiMixin
    clProp_entails clProp_emp clProp_pure clProp_and clProp_or clProp_impl
    (@clProp_forall) (@clProp_exist) clProp_sep clProp_wand.
Proof.
  split.
  - exact: entails_po.
  - exact: equiv_spec.
  - exact: pure_ne.
  - exact: and_ne.
  - exact: or_ne.
  - exact: impl_ne.
  - exact: forall_ne.
  - exact: exist_ne.
  - exact: and_ne.
  - exact: impl_ne.
  - exact: pure_intro.
  - exact: pure_elim'.
  - exact: and_elim_l.
  - exact: and_elim_r.
  - exact: and_intro.
  - exact: or_intro_l.
  - exact: or_intro_r.
  - exact: or_elim.
  - exact: impl_intro_r.
  - exact: impl_elim_l'.
  - exact: @forall_intro.
  - exact: @forall_elim.
  - exact: @exist_intro.
  - exact: @exist_elim.
  - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *)
    intros P P' Q Q' H1 H2. apply and_intro.
    + by etrans; first apply and_elim_l.
    + by etrans; first apply and_elim_r.
  - (* P ⊢ emp ∗ P *)
    intros P. apply and_intro; last done. by apply pure_intro.
  - (* emp ∗ P ⊢ P *)
    intros P. apply and_elim_r.
  - (* P ∗ Q ⊢ Q ∗ P *)
    intros P Q. apply and_intro.
    + apply and_elim_r.
    + apply and_elim_l.
  - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *)
    intros P Q R. repeat apply and_intro.
    + etrans; first apply and_elim_l. by apply and_elim_l.
    + etrans; first apply and_elim_l. by apply and_elim_r.
    + apply and_elim_r.
  - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *)
    apply impl_intro_r.
  - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *)
    apply impl_elim_l'.
Qed.

Lemma clProp_bi_persistently_mixin :
  BiPersistentlyMixin
    clProp_entails clProp_emp clProp_and
    clProp_sep clProp_persistently.
Proof.
  split.
  - solve_proper.
  - (* (P ⊢ Q) → <pers> P ⊢ <pers> Q *)
    done.
  - (* <pers> P ⊢ <pers> <pers> P *)
    done.
  - (* emp ⊢ <pers> emp *)
    done.
  - (* (∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a) *)
    done.
  - (* <pers> P ∗ Q ⊢ <pers> P *)
    apply and_elim_l.
  - (* <pers> P ∧ Q ⊢ P ∗ Q *)
    done.
Qed.

Lemma clProp_bi_later_mixin :
  BiLaterMixin
    clProp_entails clProp_pure clProp_or clProp_impl
    (@clProp_forall) (@clProp_exist) clProp_sep clProp_persistently clProp_later.
Proof.
  eapply bi_later_mixin_True;
    [done..|apply clProp_bi_mixin|apply clProp_bi_persistently_mixin].
Qed.

Canonical Structure clPropI : bi :=
  {| bi_ofe_mixin := ofe_mixin_of clProp;
     bi_bi_mixin := clProp_bi_mixin;
     bi_bi_persistently_mixin := clProp_bi_persistently_mixin;
     bi_bi_later_mixin := clProp_bi_later_mixin |}.

Global Instance clProp_persistently_forall : BiPersistentlyForall clPropI.
Proof. done. Qed.
Global Instance clProp_persistently_exist : BiPersistentlyExist clPropI.
Proof. done. Qed.

(** extra BI instances *)

Global Instance clProp_affine : BiAffine clPropI | 0.
Proof. intros P. exact: pure_intro. Qed.
(* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [BiAffine] as a premise. *)
Global Hint Immediate clProp_affine : core.

Global Instance clProp_persistent (P : clProp) : Persistent P.
Proof. done. Qed.

Module clProp.
Section restate.
  (** Classical principles *)
  Lemma dn (P : clProp) : ¬¬P ⊢ P.
  Proof. apply dn. Qed.

  (** Soundness lemma *)
  Lemma pure_soundness φ : (⊢@{clPropI} ⌜ φ ⌝) → ¬¬φ.
  Proof. apply pure_soundness. Qed.
End restate.

Section derived.
  (** Soundness lemma *)
  Lemma pure_soundness_dec φ `{!Decision φ} : (True ⊢@{clPropI} ⌜ φ ⌝) → φ.
  Proof. intros. by apply dec_stable, pure_soundness. Qed.
End derived.
End clProp.
