From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.algebra Require Import excl agree csum.
From iris.heap_lang Require Import notation par proofmode.
From iris.proofmode Require Import proofmode.
From iris_examples.barrier Require Import proof specification.
From iris.prelude Require Import options.

Definition one_shotR (Σ : gFunctors) (F : oFunctor) :=
  csumR (exclR unitO) (agreeR $ laterO $ oFunctor_apply F (iPropO Σ)).
Definition Pending {Σ F} : one_shotR Σ F := Cinl (Excl ()).
Definition Shot {Σ} {F : oFunctor} (x : oFunctor_apply F (iPropO Σ)) : one_shotR Σ F :=
  Cinr $ to_agree $ Next $ x.

Class oneShotG (Σ : gFunctors) (F : oFunctor) :=
  one_shot_inG :: inG Σ (one_shotR Σ F).
Definition oneShotΣ (F : oFunctor) : gFunctors :=
  #[ GFunctor (csumRF (exclRF unitO) (agreeRF (▶ F))) ].
Global Instance subG_oneShotΣ {Σ F} : subG (oneShotΣ F) Σ → oneShotG Σ F.
Proof. solve_inG. Qed.

Definition client : val :=
  λ: "fM" "fW1" "fW2",
  let: "b" := newbarrier #() in
  ("fM" #() ;; signal "b") ||| ((wait "b" ;; "fW1" #()) ||| (wait "b" ;; "fW2" #())).

Section proof.
Local Set Default Proof Using "Type*".
Context `{!heapGS Σ, !barrierG Σ, !spawnG Σ, !oneShotG Σ F}.
Context (N : namespace).
Local Notation X := (oFunctor_apply F (iPropO Σ)).

Definition barrier_res γ (Φ : X → iProp Σ) : iProp Σ :=
  (∃ x, own γ (Shot x) ∗ Φ x)%I.

Lemma worker_spec e γ l (Φ Ψ : X → iProp Σ) :
  recv N l (barrier_res γ Φ) -∗ (∀ x, Φ x -∗ WP e {{ _, Ψ x }}) -∗
  WP wait #l ;; e {{ _, barrier_res γ Ψ }}.
Proof.
  iIntros "Hl He". wp_apply (wait_spec with "Hl"); simpl.
  iDestruct 1 as (x) "[#Hγ Hx]".
  wp_seq. iApply (wp_wand with "[Hx He]"); [by iApply "He"|].
  iIntros (v) "?"; iExists x; by iSplit.
Qed.

Context (P : iProp Σ) (Φ Φ1 Φ2 Ψ Ψ1 Ψ2 : X -n> iPropO Σ).
Context {Φ_split : ∀ x, Φ x -∗ (Φ1 x ∗ Φ2 x)}.
Context {Ψ_join  : ∀ x, Ψ1 x -∗ Ψ2 x -∗ Ψ x}.

Lemma P_res_split γ : barrier_res γ Φ -∗ barrier_res γ Φ1 ∗ barrier_res γ Φ2.
Proof.
  iDestruct 1 as (x) "[#Hγ Hx]".
  iDestruct (Φ_split with "Hx") as "[H1 H2]". by iSplitL "H1"; iExists x; iSplit.
Qed.

Lemma Q_res_join γ : barrier_res γ Ψ1 -∗ barrier_res γ Ψ2 -∗ ▷ barrier_res γ Ψ.
Proof.
  iDestruct 1 as (x) "[#Hγ Hx]"; iDestruct 1 as (x') "[#Hγ' Hx']".
  iAssert (▷ (x ≡ x'))%I as "Hxx".
  { iCombine "Hγ" "Hγ'" as "Hγ2". iClear "Hγ Hγ'".
    rewrite own_valid csum_validI /= agree_validI agree_equivI later_equivI /=.
    rewrite -{2}[x]oFunctor_map_id -{2}[x']oFunctor_map_id.
    assert (HF : oFunctor_map F (cid, cid) ≡ oFunctor_map F (iProp_fold (Σ:=Σ) ◎
        iProp_unfold, iProp_fold (Σ:=Σ) ◎ iProp_unfold)).
    { apply ne_proper; first by apply _.
      by split; intro; simpl; symmetry; apply iProp_fold_unfold. }
    rewrite (HF x). rewrite (HF x').
    rewrite !oFunctor_map_compose. iNext. by iRewrite "Hγ2". }
  iNext. iRewrite -"Hxx" in "Hx'".
  iExists x; iFrame "Hγ". iApply (Ψ_join with "Hx Hx'").
Qed.

Lemma client_spec_new (fM fW1 fW2 : val) :
  WP fM #() {{ _, ∃ x, Φ x }} -∗
  □ (∀ x, Φ1 x -∗ WP fW1 #() {{ _, Ψ1 x }}) -∗
  □ (∀ x, Φ2 x -∗ WP fW2 #() {{ _, Ψ2 x }}) -∗
  WP client fM fW1 fW2 {{ _, ∃ γ, barrier_res γ Ψ }}.
Proof using All.
  iIntros "/= Hf #Hf1 #Hf2"; rewrite /client.
  iMod (own_alloc (Pending : one_shotR Σ F)) as (γ) "Hγ"; first done.
  wp_lam. wp_pures. wp_apply (newbarrier_spec N (barrier_res γ Φ)); auto.
  iIntros (l) "[Hr Hs]".
  set (workers_post (v : val) := (barrier_res γ Ψ1 ∗ barrier_res γ Ψ2)%I).
  wp_smart_apply (par_spec  (λ _, True)%I workers_post with "[Hf Hs Hγ] [Hr]").
  - wp_lam. wp_bind (fM #()). iApply (wp_wand with "Hf").
    iIntros (v) "HP"; iDestruct "HP" as (x) "HP". wp_seq.
    iMod (own_update with "Hγ") as "Hx".
    { by apply (cmra_update_exclusive (Shot x)). }
    iApply (signal_spec with "[- $Hs]"); last auto.
    iExists x; auto.
  - iDestruct (recv_weaken with "[] Hr") as "Hr"; first by iApply P_res_split.
    iMod (recv_split with "Hr") as "[H1 H2]"; first done.
    wp_smart_apply (par_spec (λ _, barrier_res γ Ψ1)%I
                       (λ _, barrier_res γ Ψ2)%I with "[H1] [H2]").
    + wp_smart_apply (worker_spec with "H1"); auto.
    + wp_smart_apply (worker_spec with "H2"); auto.
    + auto.
  - iIntros (_ v) "[_ [H1 H2]]". iDestruct (Q_res_join with "H1 H2") as "?". auto.
Qed.
End proof.
