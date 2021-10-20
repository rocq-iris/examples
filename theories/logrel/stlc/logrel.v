From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export proofmode.
From iris_examples.logrel.stlc Require Export lang typing.
From iris.prelude Require Import options.

Reserved Notation "⟦ τ ⟧" (at level 0, τ at level 70).
Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70).
Reserved Notation "⟦ Γ ⟧*" (at level 0, Γ at level 70).

(** interp : is a unary logical relation. *)
Section logrel.
(** STLC is somewhat unusual in that we quantify over an arbitrary [irisGS] --
almost all languages need to have a specific [irisGS] instance to fix their
specific [state_interp], but STLC has no state so it does not care. *)
Context `{irisGS stlc_lang Σ}.

Fixpoint interp (τ : type) (w : val) : iProp Σ :=
  match τ with
  | TUnit => ⌜w = UnitV⌝
  | TProd τ1 τ2 => ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ ⟦ τ1 ⟧ w1 ∧ ⟦ τ2 ⟧ w2
  | TSum τ1 τ2 =>
     (∃ w1, ⌜w = InjLV w1⌝ ∧ ⟦ τ1 ⟧ w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ ⟦ τ2 ⟧ w2)
  | TArrow τ1 τ2 => □ ∀ v, ⟦ τ1 ⟧ v → WP App (# w) (# v) {{ ⟦ τ2 ⟧ }}
  end%I
where "⟦ τ ⟧" := (interp τ).

Definition interp_expr (τ : type) (e : expr) : iProp Σ :=
  WP e {{ ⟦ τ ⟧ }}%I.

Global Instance interp_persistent τ v : Persistent (⟦ τ ⟧ v).
Proof. revert v; induction τ=> v /=; apply _. Qed.

Global Instance interp_env_base_persistent Γ vs :
  TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧) Γ vs).
Proof.
  revert vs; induction Γ => vs; simpl; destruct vs; constructor; apply _.
Qed.

Definition interp_env (Γ : list type) (vs : list val) : iProp Σ :=
  (⌜length Γ = length vs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧) Γ vs)%I.

Notation "⟦ Γ ⟧*" := (interp_env Γ).

Global Instance interp_env_persistent Γ vs :
  Persistent (⟦ Γ ⟧* vs) := _.

Lemma interp_env_nil : ⊢ ⟦ [] ⟧* [].
Proof. iSplit; simpl; auto. Qed.
Lemma interp_env_cons Γ vs τ v :
    ⟦ τ :: Γ ⟧* (v :: vs) ⊣⊢ ⟦ τ ⟧ v ∗ ⟦ Γ ⟧* vs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _)) -(comm _ ⌜(_ = _)⌝%I) -assoc.
    by apply bi.sep_proper; [apply bi.pure_proper; lia|].
  Qed.

Lemma interp_env_length Γ vs : ⟦ Γ ⟧* vs ⊢ ⌜length Γ = length vs⌝.
Proof. by iIntros "[% ?]". Qed.

Lemma interp_env_Some_l Γ vs x τ :
  Γ !! x = Some τ → ⟦ Γ ⟧* vs ⊢ ∃ v, ⌜vs !! x = Some v⌝ ∧ ⟦ τ ⟧ v.
Proof.
  iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
  destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
  { by rewrite -Hlen; apply lookup_lt_Some with τ. }
  iExists v; iSplit; first done. iApply (big_sepL_elem_of with "HΓ").
  apply elem_of_list_lookup_2 with x.
  rewrite lookup_zip_with; by simplify_option_eq.
Qed.

End logrel.

Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr τ).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
