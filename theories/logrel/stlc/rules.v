From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export proofmode.
From iris.program_logic Require Import ectx_lifting.
From iris_examples.logrel.stlc Require Export lang.
From stdpp Require Import fin_maps.
From iris.prelude Require Import options.

Section stlc_rules.
  (** STLC is somewhat unusual in that we quantify over an arbitrary [irisGS] --
  almost all languages need to have a specific [irisGS] instance to fix their
  specific [state_interp], but STLC has no state so it does not care. *)
  Context `{irisGS stlc_lang Σ}.
  Implicit Types e : expr.

  Ltac inv_base_step :=
    repeat match goal with
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : base_step ?e _ _ _ _ _ |- _ =>
       try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
       and can thus better be avoided. *)
       inversion H; subst; clear H
    end.

  Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors base_step : core.
  Local Hint Resolve to_of_val : core.

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  Local Ltac solve_pure_exec :=
    unfold IntoVal in *;
    repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
    intros ?; apply nsteps_once, pure_base_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  (** Helper Lemmas for weakestpre. *)

  Global Instance pure_lam e1 e2 `{!AsVal e2}:
    PureExec True 1 (App (Lam e1) e2) (e1.[e2 /]).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2}:
    PureExec True 1 (Fst (Pair e1 e2)) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2}:
    PureExec True 1 (Snd (Pair e1 e2)) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
  Proof. solve_pure_exec. Qed.

End stlc_rules.
