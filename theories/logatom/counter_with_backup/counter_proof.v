From iris.algebra Require Import gmap gset excl auth list.
From iris.base_logic Require Import ghost_map ghost_var mono_nat.
From iris.bi.lib Require Import fractional.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation atomic_heap.
From iris_examples.logatom.counter_with_backup Require Import counter_spec.
From iris.prelude Require Import options.

(** * Implementation of the concurrent counter spec with logical atomicity, using unsolicited helping *)
(** For a detailed explanation of the proof, we refer to the technical documentation. *)

(** As explained in the paper, we build upon the abstract logically-atomic heap defined in [atomic_heap.v], not HeapLang's built-in heap primitives. *)

Section counter_impl.
  Context {Σ : gFunctors} `{!heapGS Σ, !atomic_heap}.
  Import atomic_heap.notation.
  (** ** Definition of the operations. *)

  (** The backup thread repeatedly reads from [p] and stores it in [b]. *)
  Definition backup_thread : val :=
    rec: "backup" "c" :=
      let: "b" := Fst "c" in
      let: "p" := Snd "c" in
      let: "n" := ! "p" in
      "b" <- "n";;
      "backup" "c".

  (** Wait for the backup thread to catch up *)
  Definition await_backup : val :=
    rec: "await" "b" "n" :=
      if: !"b" < "n" then "await" "b" "n" else #().


  (** Create a new counter *)
  Definition new_counter : val :=
    λ: <>,
      let: "b" := ref #0 in (* backup *)
      let: "p" := ref #0 in (* primary *)
      Fork (backup_thread ("b", "p"));;
      ("b", "p").


  (** Increment the counter *)
  Definition increment : val :=
    λ: "c",
      let: "n" := FAA (Snd "c") #1 in
      await_backup (Fst "c") ("n" + #1);;
      "n".

  (** Get the counter value *)
  Definition get : val :=
    λ: "c",
      let: "n" := !(Snd "c") in
      await_backup (Fst "c") "n";;
      "n".

  (** Get the backup value *)
  Definition get_backup : val :=
    λ: "c",
      !(Fst "c").

End counter_impl.

(** ** Ghost state for the counter *)
Class counterG (Σ : gFunctors) := {
  counter_nat_gname_mapG :> ghost_mapG Σ nat gname;
  counter_nat_gnames_mapG :> ghost_mapG Σ nat (gname * gname);
  counter_ghost_varG :> ghost_varG Σ bool;
  counter_mono_natG :> mono_natG Σ;
  counter_tokenG :> inG Σ (exclR unitO);
  counter_ghost_setG :> ghost_mapG Σ (gname * gname) unit;
}.

Definition counterΣ : gFunctors :=
  #[GFunctor (exclR unitO);
    ghost_mapΣ nat gname;
    ghost_mapΣ nat (gname * gname);
    ghost_varΣ bool;
    mono_natΣ;
    ghost_mapΣ (gname * gname) unit].

Global Instance subG_counterΣ {Σ} : subG counterΣ Σ → counterG Σ.
Proof. solve_inG. Qed.


Section counter_proof.
  Context {Σ: gFunctors}.
  Context `{!heapGS Σ}
          `{!atomic_heap}
          `{!counterG Σ}.
  Context (N: namespace).
  Import atomic_heap.notation.

  (** ** Invariants *)

  Definition getN := N .@ "get".
  Definition putN := N .@ "put".
  Definition mainN := N .@ "main".

  Definition counter_int γ_cnt n := (mono_nat_auth_own γ_cnt (1/4) n)%I.

  Definition value '(γ_cnt, γ_ex) n := (mono_nat_auth_own γ_cnt (1/4) n ∗ own γ_ex (Excl ()))%I.

  (** Invariant for transfer of atomic update (helping) of [get] *)
  Definition get_inv γs (γ1 γ2 : gname) (n : nat) (Φ : val → iProp Σ) : iProp Σ :=
    ((AU << ∃∃ n: nat, value γs n >> @ ⊤ ∖ ↑N, ∅ << value γs n, COMM (Φ #n) >> ∗ ghost_var γ1 (1/2) true ∗ £ 1) ∨
     (ghost_var γ1 (1/2) false ∗ Φ #n) ∨ (ghost_var γ1 (1/2) false ∗ own γ2 (Excl ()))).

  (** Invariant for transfer of atomic update (helping) of [put] *)
  Definition put_inv γs (γ1 γ2 : gname) (n : nat) (Φ : val → iProp Σ): iProp Σ :=
    ((AU  << ∃∃ n: nat, value γs n >> @ ⊤ ∖ ↑N, ∅ << value γs (n + 1), COMM (Φ #n) >> ∗ ghost_var γ1 (1/2) true ∗ £ 1) ∨
     (ghost_var γ1 (1/2) false ∗ Φ #n) ∨ (ghost_var γ1 (1/2) false ∗ own γ2 (Excl ()))).

  (** The part of the main counter invariant that controls execution of [put]s *)
  Definition counter_inv_puts γs P n_b n_p : iProp Σ :=
    (⌜list_to_set (seq 0 n_p) = dom P⌝ ∗
    [∗ map] n ↦ p ∈ P, ∃ Φ, inv putN (put_inv γs (fst p) (snd p) n Φ) ∗ ghost_var (fst p) (1/2) (bool_decide (n_b ≤ n): bool))%I.

  (** The part of the main counter invariant that controls execution of [get]s *)
  Definition counter_inv_gets γs G n_b : iProp Σ:=
   ([∗ map] n ↦ γ ∈ G, ∃ (O: gset (gname * gname)), ghost_map_auth γ 1 (gset_to_gmap () O) ∗
        [∗ set] p ∈ O, ∃ Φ, inv getN (get_inv γs (fst p) (snd p) n Φ) ∗ ghost_var (fst p) (1/2) (bool_decide (n_b < n): bool))%I.

  (** The core of the main counter invariant, controlling all the authoritative ghost state *)
  Definition counter_inv_inner γs (γ_prim γ_get γ_put : gname) (b p : loc) (G : gmap nat gname) (P : gmap nat (gname * gname)) (n_b n_p : nat) : iProp Σ :=
    ⌜n_b ≤ n_p⌝ ∗ b ↦ #n_b ∗ p ↦ #n_p ∗
    (* ghost state controlling the primary and backup values *)
    counter_int (fst γs) n_b ∗ mono_nat_auth_own γ_prim 1 n_p ∗
    (* ghost state for providing ghost names for individual set/get operations *)
    ghost_map_auth γ_get 1 G ∗ ([∗ map] n ↦ γ ∈ G, n ↪[γ_get]□ γ) ∗ ghost_map_auth γ_put 1 P ∗
    (* control of [get] operations *)
    counter_inv_gets γs G n_b ∗
    (* control of [put] operations *)
    counter_inv_puts γs P n_b n_p.

  (** The main top-level counter invariant *)
  Definition counter_inv γs (γ_prim γ_get γ_put: gname) (b p: loc) : iProp Σ :=
    ∃ G P n_b n_p, counter_inv_inner γs γ_prim γ_get γ_put b p G P n_b n_p.

  (** Assertion that [c] represents a counter [γs] *)
  Definition is_counter γs (c: val): iProp Σ :=
    ∃ (b p: loc) (γ_prim γ_get γ_put: gname), ⌜c = (#b, #p)%V⌝ ∗ inv mainN (counter_inv γs γ_prim γ_get γ_put b p).

  (** ** Lemmas about the invariant that will be used by the main proofs *)
  Lemma logically_execute_put γ_cnt γ_ex P n n_p :
    n < n_p →
    counter_inv_puts (γ_cnt, γ_ex) P n n_p -∗
    counter_int γ_cnt n -∗
    counter_int γ_cnt n -∗
    counter_int γ_cnt n ={⊤ ∖ ↑mainN}=∗
    counter_inv_puts (γ_cnt, γ_ex) P (S n) n_p ∗
    counter_int γ_cnt (S n) ∗
    counter_int γ_cnt (S n) ∗
    counter_int γ_cnt (S n).
  Proof.
    rewrite /counter_inv_puts. iIntros (Hlt) "Hmap Hc1 Hc2 Hc3".
    iDestruct "Hmap" as "(%Hdom & Hmap)".
    assert (n ∈ dom P) as Hdom'.
    { rewrite -Hdom. eapply elem_of_list_to_set, elem_of_seq. lia. }
    eapply elem_of_dom in Hdom' as [[γ1 γ2] Hlook].
    rewrite big_sepM_delete //.
    iDestruct "Hmap" as "[Hput Hmap]".
    iDestruct "Hput" as (Φ) "(#I & Hvar)".
    rewrite bool_decide_decide; destruct decide; last lia.
    iInv "I" as "[[AU [>Hvar' >Hc]]|[[>Hvar' Post]|[>Hvar' >Done]]]" "Hclose";
      first last.
    - iDestruct (ghost_var_agree with "Hvar Hvar'") as "%". naive_solver.
    - iDestruct (ghost_var_agree with "Hvar Hvar'") as "%". naive_solver.
    - iMod (lc_fupd_elim_later with "Hc AU") as "AU".
      iMod "AU" as (n') "[[Hc4 Hex] [_ Hclose']]".
      iDestruct (mono_nat_auth_own_agree with "Hc1 Hc4") as "%".
      replace n' with n by naive_solver.
      iCombine "Hc1 Hc2 Hc3 Hc4" as "Hc".
      rewrite Qp.add_assoc !Qp.quarter_quarter Qp.half_half.
      iMod (mono_nat_own_update (S n) with "Hc") as "[Hc _]"; first lia.
      rewrite -{4}Qp.half_half -{4 5}Qp.quarter_quarter. iDestruct "Hc" as "[[Hc1 Hc2] [Hc3 Hc4]]".
      iFrame "Hc1 Hc2 Hc3". replace (n + 1) with (S n) by lia. iMod ("Hclose'" with "[$Hc4 $Hex]") as "HΦ".
      iMod (ghost_var_update_halves with "Hvar Hvar'") as "[Hvar Hvar']".
      iMod ("Hclose" with "[Hvar HΦ]") as "_".
      { iNext. iRight. iLeft. iFrame. }
      iModIntro. iSplit; first done.
      rewrite (big_sepM_delete _ P) //.
      iSplitL "Hvar'".
      { iExists Φ. iFrame "I". rewrite bool_decide_decide; destruct decide; first lia.
        iFrame. }
      iApply (big_sepM_impl with "Hmap"). iModIntro.
      iIntros (k [γ1' γ2'] Hel). iDestruct 1 as (Ψ) "(I' & Hvar & Hcred)".
      iExists Ψ. iFrame "I'". rewrite !bool_decide_decide.
      destruct decide, decide; [| | lia |].
      + iFrame.
      + assert (n = k) as -> by lia. rewrite lookup_delete in Hel. naive_solver.
      + iFrame.
  Qed.

  Lemma logicall_execute_gets_set γ_cnt γ_ex n O :
    (⊢ (counter_int γ_cnt (S n) ∗ [∗ set] p ∈ O, ∃ Φ, inv getN (get_inv (γ_cnt, γ_ex) p.1 p.2 (S n) Φ) ∗  ghost_var p.1 (1 / 2) true) ={⊤∖↑mainN}=∗
    counter_int γ_cnt (S n) ∗ [∗ set] p ∈ O, ∃ Φ, inv getN (get_inv (γ_cnt, γ_ex) p.1 p.2 (S n) Φ) ∗  ghost_var p.1 (1 / 2) false)%I.
  Proof.
    induction (set_wf O) as [O _ IH].
    iIntros "Hset". destruct (decide (O = ∅)) as [->|[i Hi]%set_choose_L].
    - rewrite !big_sepS_empty. done.
    - rewrite !(big_sepS_delete _ O) //.
      iDestruct "Hset" as "(Hcnt & Hi & Hrest)".
      iDestruct "Hi" as (Φ) "(#I & Hvar)".
      iInv "I" as "[[AU [>Hvar' >Hc]]|[[>Hvar' Post]|[>Hvar' >Done]]]" "Hclose"; first last.
      + iDestruct (ghost_var_agree with "Hvar Hvar'") as "%". naive_solver.
      + iDestruct (ghost_var_agree with "Hvar Hvar'") as "%". naive_solver.
      + iMod (lc_fupd_elim_later with "Hc AU") as "AU".
        iMod "AU" as (n') "[[Hcnt' Hex] [_ Hclose']]".
        iDestruct (mono_nat_auth_own_agree with "Hcnt Hcnt'") as "%".
        replace n' with (S n) by naive_solver.
        iMod ("Hclose'" with "[$Hcnt' $Hex]") as "HΦ".
        iMod (ghost_var_update_halves with "Hvar Hvar'") as "[Hvar Hvar']".
        iMod ("Hclose" with "[Hvar HΦ]") as "_".
        { iNext. iRight. iLeft. iFrame. }
        iMod (IH with "[$Hcnt $Hrest]") as "[$ $]"; first set_solver.
        iModIntro. iExists Φ. iFrame "Hvar' I".
  Qed.

  Lemma logically_execute_gets γ_cnt γ_ex G n :
    counter_inv_gets (γ_cnt, γ_ex) G n ∗ counter_int γ_cnt (S n) ={⊤ ∖ ↑mainN}=∗
    counter_inv_gets (γ_cnt, γ_ex) G (S n) ∗ counter_int γ_cnt (S n).
  Proof.
    rewrite /counter_inv_gets.
    iIntros "[Hgets Hc]".
    destruct (G !! (S n)) as [γ|] eqn: Hlook.
    - rewrite !(big_sepM_delete _ G) //.
      iDestruct "Hgets" as "[Hget Hgets]".
      rewrite bool_decide_decide; destruct decide; last lia.
      rewrite bool_decide_decide; destruct decide; first lia.
      iDestruct "Hget" as (O) "[Hmap Hset]".
      iMod (logicall_execute_gets_set with "[$Hc $Hset]") as "[Hc Hset]".
      iModIntro. iFrame. iSplitL "Hset Hmap".
      { iExists O. iFrame. }
      iApply (big_sepM_impl with "Hgets"). iModIntro.
      iIntros (k γ' Hel). iDestruct 1 as (O') "(Hmap & Hset)".
      iExists O'. iFrame. iApply (big_sepS_impl with "Hset").
      iModIntro. iIntros ([γ1' γ2'] Hel'). iDestruct 1 as (Ψ) "(I' & Hvar & Hcred)".
      iExists Ψ. iFrame "I'". rewrite !bool_decide_decide.
      destruct decide, decide; [iFrame| | lia | iFrame].
      assert (S n = k) as Heq by lia. rewrite Heq lookup_delete in Hel.
      naive_solver.
    - eapply delete_notin in Hlook. rewrite -Hlook. iModIntro. iFrame.
      iApply (big_sepM_impl with "Hgets"). iModIntro.
      iIntros (k γ' Hel). iDestruct 1 as (O') "(Hmap & Hset)".
      iExists O'. iFrame. iApply (big_sepS_impl with "Hset").
      iModIntro. iIntros ([γ1' γ2'] Hel'). iDestruct 1 as (Ψ) "(I' & Hvar & Hcred)".
      iExists Ψ. iFrame "I'". rewrite !bool_decide_decide.
      destruct decide, decide; [iFrame| | lia | iFrame].
      assert (S n = k) as Heq by lia. rewrite Heq lookup_delete in Hel.
      naive_solver.
  Qed.

  Lemma logically_execute_gets_and_puts γ_cnt γ_ex P G n_b n n_p:
    n_b ≤ n ≤ n_p →
    counter_inv_puts (γ_cnt, γ_ex) P n_b n_p -∗
    counter_inv_gets (γ_cnt, γ_ex) G n_b -∗
    counter_int γ_cnt n_b -∗
    counter_int γ_cnt n_b -∗
    counter_int γ_cnt n_b ={⊤ ∖ ↑mainN}=∗
    counter_inv_puts (γ_cnt, γ_ex) P n n_p ∗
    counter_inv_gets (γ_cnt, γ_ex) G n ∗
    counter_int γ_cnt n ∗
    counter_int γ_cnt n ∗
    counter_int γ_cnt n.
  Proof.
    intros [Hle1 Hle2].
    induction Hle1 as [|n Hle1 IH].
    - by iIntros "$ $ $ $ $".
    - iIntros "Hputs Hgets Hc1 Hc2 Hc3".
      iMod (IH with "Hputs Hgets Hc1 Hc2 Hc3") as "(Hputs & Hgets & Hc1 & Hc2 & Hc3)"; first lia; clear IH.
      iMod (logically_execute_put with "Hputs Hc1 Hc2 Hc3") as "(Hputs & Hc1 & Hc2 & Hc3)"; first lia.
      iMod (logically_execute_gets with "[$Hgets $Hc1]") as "(Hgets & Hc1)".
      iModIntro. iFrame.
  Qed.

  Lemma counter_inv_inner_add_get_set E γs γ_prim γ_get γ_put b p G P n n_b n_p :
    G !! n = None →
    counter_inv_inner γs γ_prim γ_get γ_put b p G P n_b n_p ={E}=∗
    ∃ γ, counter_inv_inner γs γ_prim γ_get γ_put b p (<[n := γ]> G) P n_b n_p ∗ n ↪[γ_get]□ γ.
  Proof.
    iIntros (Hlook) "Cnt". iDestruct "Cnt" as "(% & Hb & Hp & Hmon & Hprim & HG & #Hlook & HP & Hget & Hput)".
    iMod (ghost_map_alloc (gset_to_gmap () ∅)) as (γ) "[Hmap _]".
    iMod (ghost_map_insert_persist n γ with "HG") as "[HG #Hlook']"; first done.
    iModIntro. iExists γ. rewrite /counter_inv_inner /counter_inv_gets. iFrame.
    iSplitR ""; last done.
    iSplit; first done. rewrite !big_sepM_insert //.
    iFrame. iSplitR; first eauto with iFrame.
    iExists ∅. iFrame.
    rewrite big_sepS_empty. done.
  Qed.


  Lemma counter_inv_inner_ensure_getter E γs γ_prim γ_get γ_put b p G P (n: nat) n_b n_p :
    counter_inv_inner γs γ_prim γ_get γ_put b p G P n_b n_p ={E}=∗
    ∃ G' (γ: gname), counter_inv_inner γs γ_prim γ_get γ_put b p G' P n_b n_p ∗ n ↪[ γ_get ]□ γ.
  Proof.
    destruct (G !! n) as [γ|] eqn: Hγ.
    - iIntros "Cnt". iDestruct "Cnt" as "(Hle & Hb & Hp & Hmon & Hprim & HG & #Hlook & HP & Hget & Hput)".
      iModIntro. iExists G, γ. rewrite /counter_inv_inner /counter_inv_gets. iFrame.
      iSplit; first done. by iApply (big_sepM_lookup with "Hlook").
    - iIntros "H". iMod (counter_inv_inner_add_get_set with "H") as (γ) "(Hi & Hlook)"; first done.
      iModIntro. iExists _, γ. iFrame.
  Qed.

  Lemma counter_inv_inner_register_get Φ E γs γ_prim γ_get γ_put γ b p G P n_b n_p :
    n_b < n_p →
    AU << ∃∃ n: nat, value γs n >> @ ⊤ ∖ ↑N, ∅ << value γs n, COMM (Φ #n) >> -∗
    £ 1 -∗
    n_p ↪[ γ_get ]□ γ -∗
    counter_inv_inner γs γ_prim γ_get γ_put b p G P n_b n_p ={E}=∗
    counter_inv_inner γs γ_prim γ_get γ_put b p G P n_b n_p ∗ ∃ (γ_1 γ_2: gname), (γ_1, γ_2) ↪[γ]□ () ∗ inv getN (get_inv γs γ_1 γ_2 n_p Φ) ∗ own γ_2 (Excl ()).
  Proof.
    iIntros (Hlt) "AU Hcred Hlook' Cnt". iDestruct "Cnt" as "(% & Hb & Hp & Hmon & Hprim & HG & #Hlook & HP & Hget & Hput)".
    iDestruct (ghost_map_lookup with "HG Hlook'") as "%".
    iPoseProof (big_sepM_lookup_acc with "Hget") as "[Hel Hget]"; first done.
    iDestruct "Hel" as (O) "(Hmap & Hset)".
    (* we allocate the two ghost names γ1 and γ2 *)
    iMod (ghost_var_alloc_strong true (λ γ, ∀ γ2: gname, (γ, γ2) ∉ O)) as (γ1 Hfresh1) "Hg".
    { rewrite /pred_infinite. intros xs. pose (γ1 := fresh (xs ++ (fst <$> elements O))).
      exists γ1; split.
      - intros γ2. intros Hel. eapply (infinite_is_fresh (xs ++ (elements O).*1)).
        eapply elem_of_app; right. eapply elem_of_list_fmap_1_alt; first eapply elem_of_elements, Hel.
        done.
      - intros Hel. eapply (infinite_is_fresh (xs ++ (elements O).*1)).
        eapply elem_of_app; left. eapply Hel. }
    iDestruct "Hg" as "[Hγ1 Hγ1']".
    iMod (own_alloc (Excl ())) as (γ2) "Hγ2"; first done.
    (* we allocate the invariant *)
    iMod (inv_alloc getN E (get_inv γs γ1 γ2 n_p Φ) with "[Hγ1 AU Hcred]") as "#Iget".
    { iNext. iLeft. iFrame. }
    iMod (ghost_map_insert_persist (γ1, γ2) () with "Hmap") as "[Hmap #Hlook'']".
    { eapply lookup_gset_to_gmap_None, Hfresh1. }
    rewrite -gset_to_gmap_union_singleton. iModIntro.
    iSplitR "Hγ2".
    + iSpecialize ("Hget" with "[Hγ1' Hmap Hset]").
      { iExists (({[(γ1, γ2)]} ∪ O)). iFrame.
        rewrite big_sepS_union; last set_solver. iFrame.
        rewrite big_sepS_singleton. iExists Φ. iFrame.
        simpl. iSplitR; first done. rewrite bool_decide_decide.
        destruct decide; last lia. iFrame. }
      rewrite /counter_inv_inner. iFrame.
      iSplit; done.
    + iExists γ1, γ2. iFrame. repeat iSplit; done.
  Qed.

  Lemma counter_inv_inner_register_put Φ E γs γ_prim γ_get γ_put b p G P n_b n_p :
    n_b ≤ n_p →
    AU << ∃∃ n: nat, value γs n >> @ ⊤ ∖ ↑N, ∅ << value γs (n + 1), COMM (Φ #n) >> -∗
    £ 1 -∗
    b ↦ #n_b -∗
    p ↦ #(S n_p) -∗
    counter_int (fst γs) n_b -∗
    mono_nat_auth_own γ_prim 1 n_p -∗
    ghost_map_auth γ_get 1 G -∗
    ([∗ map] n↦γ ∈ G, n ↪[ γ_get ]□ γ) -∗
    ghost_map_auth γ_put 1 P -∗
    counter_inv_gets γs G n_b -∗
    counter_inv_puts γs P n_b n_p ={E}=∗
    ∃ γ1 γ2, counter_inv_inner γs γ_prim γ_get γ_put b p G (<[n_p := (γ1, γ2)]> P) n_b (S n_p) ∗ n_p ↪[γ_put]□ (γ1, γ2) ∗ inv putN (put_inv γs γ1 γ2 n_p Φ) ∗ own γ2 (Excl ()).
  Proof.
    iIntros (Hle) "AU Hcred Hb Hp Hmon Hprim HG #Hlook HP Hget [%Hdom Hput]".
    assert (P !! n_p = None) as Hlook.
    { eapply not_elem_of_dom. rewrite -Hdom. intros Hel%elem_of_list_to_set%elem_of_seq. lia. }
    iMod (ghost_var_alloc true) as (γ1) "[Hγ1 Hg]".
    iMod (own_alloc (Excl ())) as (γ2) "Hγ2"; first done.
    (* we allocate the invariant *)
    iMod (inv_alloc putN E (put_inv γs γ1 γ2 n_p Φ) with "[Hγ1 AU Hcred]") as "#Iput".
    { iNext. iLeft. iFrame. }
    iMod (ghost_map_insert_persist n_p (γ1, γ2) with "HP") as "[HP #Hlook'']"; first done.
    iMod (mono_nat_own_update (S n_p) with "Hprim") as "[Hprim _]"; first lia.
    iModIntro. iExists γ1, γ2. iFrame "Hlook'' Hγ2 Iput".
    rewrite /counter_inv_inner. iFrame. iFrame "Hlook".
    iSplit; first by iPureIntro; lia.
    rewrite /counter_inv_puts.
    iSplit.
    { iPureIntro. rewrite list_to_set_seq set_seq_S_end_union_L dom_insert_L -Hdom list_to_set_seq //. }
    rewrite big_sepM_insert //. iFrame. iExists Φ. iFrame "Iput".
    rewrite bool_decide_decide; destruct decide; last lia. iFrame.
  Qed.


  (** We obtain the post condition of the AU for [get] after it has been executed,
    as asserted by the ghost state in the precondition. *)
  Lemma counter_inv_extract_get_post γ_cnt γ_ex γ_prim γ_get γ_put Φ γ γ1 γ2 b p n_p :
    £2 -∗
    own γ2 (Excl ()) -∗
    inv mainN (counter_inv (γ_cnt, γ_ex) γ_prim γ_get γ_put b p) -∗
    n_p ↪[ γ_get ]□ γ -∗
    (γ1, γ2) ↪[ γ ]□ () -∗
    inv getN (get_inv (γ_cnt, γ_ex) γ1 γ2 n_p Φ) -∗
    mono_nat_lb_own γ_cnt n_p ={⊤}=∗
    Φ #n_p.
  Proof.
    rewrite lc_succ.
    iIntros "[Hone Hone'] Hex #I #Hget #Hset #Hinv #Hlb".
    iInv "I" as "Hi" "Hclose"; simpl.
    iMod (lc_fupd_elim_later with "Hone Hi") as (G P n_b' n_p') "(Hle & Hb & Hp & Hcnt & Hprim & HG & #Hlook & HP & Hget' & Hput)".
    iDestruct (ghost_map_lookup with "HG Hget") as "%".
    rewrite /counter_inv_gets.
    rewrite (big_sepM_lookup_acc (λ k y, ∃ O, _)%I G); last done.
    iDestruct "Hget'" as "(Hget' & Hcont)".
    iDestruct "Hget'" as (O) "(Hmap & Hset')".
    iDestruct (ghost_map_lookup with "Hmap Hset") as "%Hlookup".
    eapply lookup_gset_to_gmap_Some in Hlookup as [Hel _].
    rewrite big_sepS_elem_of_acc //. iDestruct "Hset'" as "(Hel & Hset')".
    iDestruct "Hel" as (Ψ) "(I' & Hgv & Hcred)".
    rewrite {1 2}bool_decide_decide.
    destruct (decide (n_b' < n_p)).
    { iPoseProof (mono_nat_lb_own_valid with "Hcnt Hlb") as "[_ %]".
      lia. }
    iInv "Hinv" as "Hi" "Hclose'".
    iMod (lc_fupd_elim_later with "Hone' Hi") as "[AU|[Post|Done]]".
    - iDestruct "AU" as "[AU [Hvar Hc]]".
      (* contradictory *)
      iPoseProof (ghost_var_agree with "Hgv Hvar") as "%".
      naive_solver.
    - iDestruct "Post" as "[Hvar $]".
      iMod ("Hclose'" with "[Hvar Hex]") as "_"; first by iRight; iRight; iFrame.
      iApply "Hclose". iNext. iExists G, P, n_b', n_p'.
      iFrame. iSplit; first done.
      iApply "Hcont". iExists O. iFrame. iApply "Hset'".
      iExists Ψ. rewrite bool_decide_eq_false_2 //. iFrame.
    - iDestruct "Done" as "[_ Htok]".
      (* contradictory *)
      iCombine "Hex Htok" gives %[].
  Qed.

  (** We obtain the post condition of the AU for [put] after it has been executed,
    as asserted by the ghost state in the precondition *)
  Lemma counter_inv_extract_put_post γ_cnt γ_ex γ_prim γ_get γ_put Φ γ1 γ2 b p n_p :
    £2 -∗
    own γ2 (Excl ()) -∗
    inv mainN (counter_inv (γ_cnt, γ_ex) γ_prim γ_get γ_put b p) -∗
    n_p ↪[ γ_put ]□ (γ1, γ2) -∗
    inv putN (put_inv (γ_cnt, γ_ex) γ1 γ2 n_p Φ) -∗
    mono_nat_lb_own γ_cnt (S n_p) ={⊤}=∗
    Φ #n_p.
  Proof.
    rewrite lc_succ.
    iIntros "[Hone Hone'] Hex #I #Hget #Hinv #Hlb".
    iInv "I" as "Hi" "Hclose"; simpl.
    iMod (lc_fupd_elim_later with "Hone Hi") as (G P n_b' n_p') "(Hle & Hb & Hp & Hcnt & Hprim & HG & #Hlook & HP & Hget' & Hput)".
    iDestruct (ghost_map_lookup with "HP Hget") as "%".
    rewrite /counter_inv_puts.
    rewrite (big_sepM_lookup_acc _ P); last done.
    iDestruct "Hput" as "(% & Hput & Hcont)".
    iDestruct "Hput" as (Ψ) "(I' & Hgv & Hcred)".
    rewrite {1 2}bool_decide_decide.
    destruct (decide).
    { iPoseProof (mono_nat_lb_own_valid with "Hcnt Hlb") as "[_ %]".
      lia. }
    iInv "Hinv" as "Hi" "Hclose'".
    iMod (lc_fupd_elim_later with "Hone' Hi") as "[AU|[Post|Done]]".
    - iDestruct "AU" as "[AU [Hvar Hc]]".
      iPoseProof (ghost_var_agree with "Hgv Hvar") as "%".
      naive_solver.
    - iDestruct "Post" as "[Hvar $]".
      iMod ("Hclose'" with "[Hvar Hex]") as "_"; first by iRight; iRight; iFrame.
      iApply "Hclose". iNext. iExists G, P, n_b', n_p'.
      iFrame. iSplit; first done. rewrite /counter_inv_puts.
      iSplit; first done.
      iApply "Hcont". iExists Ψ.
      rewrite bool_decide_eq_false_2 //.
      iFrame.
    - iDestruct "Done" as "[_ Htok]".
      iCombine "Hex Htok" gives %[].
  Qed.

  (** ** Proving the actual specs for the counter operations *)
  (** *** Specs for the helper functions *)
  Lemma backup_thread_spec γ_cnt γ_ex γ_prim γ_get γ_put n (b p : loc):
    inv mainN (counter_inv (γ_cnt, γ_ex) γ_prim γ_get γ_put b p) -∗
    counter_int γ_cnt n -∗
    counter_int γ_cnt n -∗
    WP backup_thread (#b, #p)%V {{ _, True }}.
  Proof.
    iIntros "#I". iRevert (n). iLöb as "IH". iIntros (n) "Cnt Cnt2".
    rewrite {2}/backup_thread.
    wp_pure credit:"Hone". wp_pures.
    awp_apply load_spec.
    iInv "I" as (G P n_b n_p) "(>%Hn & >Hb & >Hp & >Hcnt & >Hprim & Hrest)".
    iAaccIntro with "Hp".
    { iIntros "?". iModIntro. rewrite /counter_inv /counter_inv_inner. iFrame "Cnt Hone". iFrame. iNext. iExists G, P, n_b, n_p. eauto with iFrame. }
    iIntros "Hp". iDestruct (mono_nat_auth_own_agree with "Hcnt Cnt") as %[_ ->].
    iDestruct (mono_nat_lb_own_get with "Hprim") as "#Hn_p".
    iModIntro. iSplitR "Cnt Cnt2 Hone".
    { iNext. rewrite /counter_inv /counter_inv_inner. iExists G, P, n, n_p. eauto with iFrame. }
    wp_pures.
    awp_apply store_spec. clear -Hn.
    rewrite difference_empty_L.
    iInv "I" as (G P n_b n_p') "(>% & >Hb & >Hp & >Hcnt & >Hprim & Hrest)".
    iDestruct (mono_nat_auth_own_agree with "Hcnt Cnt") as %[_ ->].
    iDestruct (mono_nat_lb_own_valid with "Hprim Hn_p") as %[_ Hle].
    iAaccIntro with "Hb".
    { iIntros "Hb". iFrame. iModIntro. iNext. rewrite /counter_inv /counter_inv_inner.
      iExists G, P, n, n_p'. iFrame. iPureIntro. lia. }
    iIntros "Hb". iMod (lc_fupd_elim_later with "Hone Hrest") as "(HG & #Hlook & HP & Hgets & Hputs)".
    iMod (logically_execute_gets_and_puts _ _ _ _ _ n_p with "Hputs Hgets Cnt Cnt2 Hcnt") as "(Hputs & Hgets & Cnt & Cnt2 & Hcnt)"; first (split; by eauto).
    iModIntro. iSplitR "Cnt Cnt2".
    { iNext. rewrite /counter_inv /counter_inv_inner.
      iExists G, P, _, _. eauto with iFrame. }
    do 2 wp_pure. rewrite /backup_thread. iApply ("IH" with "Cnt Cnt2").
  Qed.


  Lemma await_backup_spec (γ_cnt γ_ex γ_prim γ_get γ_put : gname) (b p : loc) (n : nat) :
    inv mainN (counter_inv (γ_cnt, γ_ex) γ_prim γ_get γ_put b p) -∗
    WP (await_backup #b #n) {{ _, mono_nat_lb_own γ_cnt n }}.
  Proof.
    iIntros"#I". iLöb as "IH".
    rewrite /await_backup. wp_pures.
    awp_apply load_spec. iInv "I" as (G P n_b n_p) "(>Hle & >Hb & >Hp & >Hcnt & >Hprim & >HG &>#Hlook & >HP & Hget & Hput)".
    iAaccIntro with "Hb".
    { iIntros "Hb !>". rewrite right_id. iExists G, P, n_b, n_p.
     rewrite /counter_inv_inner. eauto with iFrame. }
    iIntros "Hb". iPoseProof (mono_nat_lb_own_get with "Hcnt") as "#Hcp".
    iModIntro. iSplitR "".
    { iExists G, P, n_b, n_p. rewrite /counter_inv_inner. eauto with iFrame.  }
    wp_pures. rewrite bool_decide_decide.
    destruct (decide (n_b < n)%Z).
    - wp_pure. done.
    - wp_pures. iModIntro.
      iApply mono_nat_lb_own_le; last done.
      lia.
  Qed.


  (** *** Proof of [get] *)
  Lemma get_spec γs (c : val) :
    is_counter γs c ⊢ <<< ∀∀ (n : nat), value γs n >>> (get c) @ ↑N <<< value γs n, RET #n>>>.
  Proof.
    iIntros "Counter". iIntros (Φ) "AU". destruct γs as [γ_cnt γ_ex].
    iDestruct "Counter" as (b p γ_prim γ_get γ_put) "(-> & #I)".
    rewrite /get.
    wp_pure credit:"Hone". wp_pure credit:"Hone'".
    awp_apply load_spec.
    iInv "I" as (G P n_b n_p) "(>% & >Hb & >Hp & Hrest)".
    iAaccIntro with "Hp".
    { iIntros "Hp". iModIntro. iFrame. iNext. rewrite /counter_inv /counter_inv_inner. iExists G, P, n_b, n_p. eauto with iFrame. }
    iIntros "Hp". iMod (lc_fupd_elim_later with "Hone' Hrest") as "(Hcnt & Hprim & HG & #Hlook & HP & Hget & Hput)".
     assert (n_b = n_p ∨ n_b < n_p) as [->|Hlt] by lia.
    - (* we are reading the latest value, we can linearize now *)
      iMod "AU" as (n) "[[Hc Hex] [_ Hclose]]".
      iDestruct (mono_nat_auth_own_agree with "Hcnt Hc") as "%".
      replace n_p with n by naive_solver. iMod ("Hclose" with "[$Hc $Hex]") as "HΦ".
      iModIntro. iSplitR "HΦ".
      { iNext. iExists G, P, n, n. rewrite /counter_inv_inner; eauto with iFrame. }
      wp_pures. wp_bind (await_backup _ _).
      iApply (wp_wand with "[]"); first by iApply await_backup_spec.
      iIntros (u) "_". by wp_pures.
    - (* we have read an old value, we will put the AU in the invariant and wait for help *)
      iMod (counter_inv_inner_ensure_getter _ _ _ _ _ _ _ _ _ n_p with "[Hb Hcnt Hprim HG HP Hget Hput Hp]") as (G' γ) "[Hinner #Hx]".
      { rewrite /counter_inv_inner. iFrame "Hcnt". iFrame "Hb Hp". iFrame "HG HP Hget Hprim Hlook Hput". done. }
      iMod (counter_inv_inner_register_get _ _ (γ_cnt, γ_ex) _ _ _ _ _ _ _ _ n_b with "AU Hone Hx [-]") as "[Hinner Hcont]"; first done.
      { iFrame. }
      iModIntro. iSplitL "Hinner"; first by iExists G', P, n_b, n_p.
      iDestruct "Hcont" as (γ1 γ2) "(#Hset & #Hinv & Hex)".
      wp_pure credit:"Hone". wp_pures.
      wp_bind (await_backup _ _).
      iApply wp_wand; first by iApply await_backup_spec.
      iIntros (u) "#Hlb". wp_pure credit:"Hone'". wp_pures.
      iCombine "Hone Hone'" as "Htwo"; simpl.
      iApply (counter_inv_extract_get_post with "Htwo Hex [//] [//] [//] [//] [//]").
  Qed.

  (** *** Proof of [get_backup] *)
  Lemma get_backup_spec γs (c: val) :
    is_counter γs c ⊢ <<< ∀∀ (n: nat), value γs n >>> (get_backup c) @ ↑N <<< value γs n, RET #n>>>.
  Proof.
    iIntros "Counter". iIntros (Φ) "AU". destruct γs as [γ_cnt γ_ex].
    iDestruct "Counter" as (b p γ_prim γ_get γ_put) "(-> & #I)".
    rewrite /get_backup. wp_pure credit:"Hone". wp_pure credit:"Hone'". wp_pures.
    awp_apply load_spec.
    iInv "I" as (G P n_b n_p) "(>% & >Hb & >Hp & Hrest)".
    iAaccIntro with "Hb".
    { iIntros "Hb". iModIntro. iFrame. iNext. rewrite /counter_inv /counter_inv_inner. iExists G, P, n_b, n_p. eauto with iFrame. }
    iIntros "Hb".
     iMod (lc_fupd_elim_later with "Hone' Hrest") as "(Hcnt & Hprim & HG & #Hlook & HP & Hget & Hput)".
     iMod "AU" as (n) "[[Hc Hex] [_ Hclose]]".
     iDestruct (mono_nat_auth_own_agree with "Hcnt Hc") as "%".
     assert (n_b = n) as -> by naive_solver. iMod ("Hclose" with "[$Hc $Hex]") as "HΦ".
     iModIntro. iSplitR "HΦ".
     { iNext. iExists G, P, n, n_p. rewrite /counter_inv_inner; eauto with iFrame. }
     done.
  Qed.

  (** *** Proof of [increment] *)
  Lemma increment_spec γs (c: val) :
    is_counter γs c ⊢ <<< ∀∀ (n: nat), value γs n >>> (increment c) @ ↑N <<< value γs (n + 1), RET #n>>>.
  Proof.
    iIntros "Counter". iIntros (Φ) "AU". destruct γs as [γ_cnt γ_ex].
    iDestruct "Counter" as (b p γ_prim γ_get γ_put) "(-> & #I)".
    rewrite /increment. wp_pure credit:"Hone". wp_pure credit:"Hone'". wp_pures.
    awp_apply faa_spec.
    iInv "I" as (G P n_b n_p) "(>% & >Hb & >Hp & Hrest)".
    iAaccIntro with "Hp".
    { iIntros "Hp". iModIntro. iFrame. iNext. rewrite /counter_inv /counter_inv_inner. iExists G, P, n_b, n_p. eauto with iFrame. }
    iIntros "Hp". iMod (lc_fupd_elim_later with "Hone' Hrest") as "(Hcnt & Hprim & HG & #Hlook & HP & Hget & Hput)".
    iMod (counter_inv_inner_register_put _ _ (γ_cnt, γ_ex) with "AU Hone Hb [Hp] Hcnt Hprim HG Hlook HP Hget Hput") as "Hupd"; first lia.
    { replace (n_p + 1)%Z with (S n_p : Z) by lia. iExact "Hp". }
    iDestruct "Hupd" as (γ1 γ2) "(Hinner & #Hlook' & #I' & Htok)".
    iModIntro. iSplitL "Hinner"; first by rewrite /counter_inv; iNext; iExists G, _, n_b, (S n_p).
    wp_pure credit:"Hone". wp_pure credit:"Hone'". wp_pures.
    wp_bind (await_backup _ _). replace (n_p + 1)%Z with (S n_p : Z) by lia.
    iApply wp_wand; first by iApply (await_backup_spec with "I").
    iIntros (u) "#Hmon".
    iMod (counter_inv_extract_put_post with "[Hone Hone'] Htok I Hlook' I' Hmon").
    { rewrite (lc_succ 1). iFrame. }
    wp_pures. done.
  Qed.

  (** *** Proof of [new_counter] *)
  Lemma new_counter_spec :
  {{{ True }}} new_counter #() {{{ c γs, RET c; is_counter γs c ∗ value γs 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /new_counter. wp_pures.
    wp_bind (ref _)%E. wp_apply alloc_spec; first done.
    iIntros (b) "Hb". wp_pures.
    wp_apply alloc_spec; first done.
    iIntros (p) "Hp". wp_pures.
    iMod (ghost_map_alloc (∅ : gmap nat (gname * gname))) as (γ_put) "[HP _]".
    iMod (ghost_map_alloc (∅ : gmap nat gname)) as (γ_get) "[HG _]".
    iMod (mono_nat_own_alloc 0) as (γ_cnt) "[Cnt _]".
    rewrite -{5}Qp.half_half -Qp.quarter_quarter Qp.add_assoc.
    iDestruct "Cnt" as "[[[C1 C2] C3] C4]".
    iMod (mono_nat_own_alloc 0) as (γ_prim) "[Hprim _]".
    iMod (own_alloc (Excl ())) as (γ_ex) "Hex"; first done.
    iMod (inv_alloc mainN _ (counter_inv (γ_cnt, γ_ex) γ_prim γ_get γ_put b p) with "[-C1 C2 C3 Hex HΦ]") as "#I".
    { iNext. iExists ∅, ∅, 0, 0. rewrite /counter_inv_inner. iFrame.
      rewrite /counter_inv_gets /counter_inv_puts !big_sepM_empty dom_empty_L //. }
    wp_bind (Fork _).
    iApply (wp_fork with "[C2 C3]").
    { iNext. wp_pures. iApply (backup_thread_spec with "I C2 C3"). }
    iNext. wp_pures. iModIntro. iApply ("HΦ" $! (#b, #p)%V (γ_cnt, γ_ex)).
    iFrame. iExists b, p, γ_prim, γ_get, γ_put. iSplit; done.
  Qed.
End counter_proof.

(** Our particular counter is an instance of the logically-atomic counter interface *)
Program Definition atomic_counter `{!heapGS Σ, counterG Σ} `{!atomic_heap} :
  atomic_counter Σ :=
  {|
      counter_spec.new_counter_spec := new_counter_spec;
      counter_spec.increment_spec := increment_spec;
      counter_spec.get_spec := get_spec;
      counter_spec.get_backup_spec := get_backup_spec;
  |}.
Next Obligation.
  intros ????[] ?. rewrite /value. apply _.
Qed.
Next Obligation.
  intros ???? [γ_cnt γ_ex] ??. iIntros "[_ H1] [_ H2]".
  iCombine "H1 H2" gives %[].
Qed.

Global Typeclasses Opaque value is_counter.
