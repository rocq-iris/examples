(** Concurrent Runner example from
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>
*)
From iris.heap_lang Require Import proofmode notation.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import cmra agree frac csum excl.
From iris.heap_lang.lib Require Import assert.
From iris_examples.hocap Require Export abstract_bag shared_bag lib.oneshot.
From iris.prelude Require Import options.

(** RA describing the evolution of a task *)
(** INIT = task has been initiated
    SET_RES v = the result of the task has been computed and it is v
    FIN v = the task has been completed with the result v *)
(* We use this RA to verify the Task.run() method *)
Definition saR := csumR fracR (csumR (prodR fracR (agreeR valO)) (agreeR valO)).
Class saG Σ := { sa_inG :: inG Σ saR }.
Definition INIT `{saG Σ} γ (q: Qp) := own γ (Cinl q%Qp).
Definition SET_RES `{saG Σ} γ (q: Qp) (v: val) := own γ (Cinr (Cinl (q%Qp, to_agree v))).
Definition FIN `{saG Σ} γ (v: val) := own γ (Cinr (Cinr (to_agree v))).
Global Instance INIT_fractional `{saG Σ} γ : Fractional (INIT γ)%I.
Proof.
  intros p q. rewrite /INIT.
  rewrite -own_op. by f_equiv.
Qed.
Global Instance INIT_as_fractional `{saG Σ} γ q:
  AsFractional (INIT γ q) (INIT γ)%I q.
Proof.
  split; [done | apply _].
Qed.
Global Instance SET_RES_fractional `{saG Σ} γ v : Fractional (fun q => SET_RES γ q v)%I.
Proof.
  intros p q. rewrite /SET_RES.
  rewrite -own_op -Cinr_op -Cinl_op -pair_op agree_idemp. by f_equiv.
Qed.
Global Instance SET_RES_as_fractional `{saG Σ} γ q v:
  AsFractional (SET_RES γ q v) (fun q => SET_RES γ q v)%I q.
Proof.
  split; [done | apply _].
Qed.

Lemma new_INIT `{saG Σ} : ⊢ |==> ∃ γ, INIT γ 1%Qp.
Proof. by apply own_alloc. Qed.
Lemma INIT_not_SET_RES `{saG Σ} γ q q' v :
  INIT γ q -∗ SET_RES γ q' v -∗ False.
Proof.
  iIntros "Hs Hp".
  iCombine "Hs Hp" gives %[].
Qed.
Lemma INIT_not_FIN `{saG Σ} γ q v :
  INIT γ q -∗ FIN γ v -∗ False.
Proof.
  iIntros "Hs Hp".
  iCombine "Hs Hp" gives %[].
Qed.
Lemma SET_RES_not_FIN `{saG Σ} γ q v v' :
  SET_RES γ q v -∗ FIN γ v' -∗ False.
Proof.
  iIntros "Hs Hp".
  iCombine "Hs Hp" gives %[].
Qed.
Lemma SET_RES_agree `{saG Σ} (γ: gname) (q q': Qp) (v w: val) :
  SET_RES γ q v -∗ SET_RES γ q' w -∗ ⌜v = w⌝.
Proof.
  iIntros "Hs1 Hs2".
  iCombine "Hs1 Hs2" gives %Hfoo.
  iPureIntro. rewrite -Cinr_op -Cinl_op -pair_op in Hfoo.
  by destruct Hfoo as [_ ?%to_agree_op_inv_L].
Qed.
Lemma FIN_agree `{saG Σ} (γ: gname) (v w: val) :
  FIN γ v -∗ FIN γ w -∗ ⌜v = w⌝.
Proof.
  iIntros "Hs1 Hs2".
  iCombine "Hs1 Hs2" gives %Hfoo.
  iPureIntro. rewrite -Cinr_op -Cinr_op in Hfoo.
  by apply to_agree_op_inv_L.
Qed.
Lemma INIT_SET_RES `{saG Σ} (v: val) γ :
  INIT γ 1%Qp ==∗ SET_RES γ 1%Qp v.
Proof.
  apply own_update.
  by apply cmra_update_exclusive.
Qed.
Lemma SET_RES_FIN `{saG Σ} (v w: val) γ :
  SET_RES γ 1%Qp v ==∗ FIN γ w.
Proof.
  apply own_update.
  by apply cmra_update_exclusive.
Qed.

Section contents.
  Context `{heapGS Σ, !oneshotG Σ, !saG Σ}.
  Variable b : bag Σ.
  Variable N : namespace.

  (* new Task : Runner<A,B> -> A -> Task<A,B> *)
  Definition newTask : val := λ: "r" "a", ("r", "a", ref #0, ref NONEV).
  (* task_runner == Fst Fst Fst *)
  (* task_arg    == Snd Fst Fst *)
  (* task_state  == Snd Fst *)
  (* task_res    == Snd *)
  (* Task.Run : Task<A,B> -> () *)
  Definition task_Run : val := λ: "t",
    let: "runner" := Fst (Fst (Fst "t")) in
    let: "arg"    := Snd (Fst (Fst "t")) in
    let: "state"  := Snd (Fst "t") in
    let: "res"    := Snd "t" in
    let: "tmp" := (Fst "runner") "runner" "arg"
                  (* runner.body(runner,arg)*) in
    "res" <- (SOME "tmp");;
    "state" <- #1.

  (* Task.Join : Task<A,B> -> B *)
  Definition task_Join : val := rec: "join" "t" :=
    let: "runner" := Fst (Fst (Fst "t")) in
    let: "arg"    := Snd (Fst (Fst "t")) in
    let: "state"  := Snd (Fst "t") in
    let: "res"    := Snd "t" in
    if: (!"state" = #1)
    then match: !"res" with
           NONE => assert #false
         | SOME "v" => "v"
         end
    else "join" "t".

  (* runner_body == Fst *)
  (* runner_bag  == Snd *)

  (* Runner.Fork : Runner<A,B> -> A -> Task<A,B> *)
  Definition runner_Fork : val := λ: "r" "a",
    let: "bag" := Snd "r" in
    let: "t" := newTask "r" "a" in
    pushBag b "bag" "t";;
    "t".

  (* Runner.runTask : Runner<A,B> -> () *)
  Definition runner_runTask : val := λ: "r",
    let: "bag" := Snd "r" in
    match: popBag b "bag" with
      NONE => #()
    | SOME "t" => task_Run "t"
    end.

  (* Runner.runTasks : Runner<A,B> -> () *)
  Definition runner_runTasks : val := rec: "runTasks" "r" :=
    runner_runTask "r";; "runTasks" "r".

  (* newRunner : (Runner<A,B> -> A -> B) -> nat -> Runner<A,B> *)
  Definition newRunner : val := λ: "body" "n",
    let: "bag" := newBag b #() in
    let: "r" := ("body", "bag") in
    let: "loop" :=
       (rec: "loop" "i" :=
          if: ("i" < "n")
          then Fork (runner_runTasks "r");; "loop" ("i"+#1)
          else "r"
       ) in
    "loop" #0.

  Definition task_inv (γ γ': gname) (state res: loc) (Q: val → iProp Σ) : iProp Σ :=
    ((state ↦ #0 ∗ res ↦ NONEV ∗ pending γ (1/2)%Qp ∗ INIT γ' (1/2)%Qp)
   ∨ (∃ v, state ↦ #0 ∗ res ↦ SOMEV v ∗ pending γ (1/2)%Qp ∗ SET_RES γ' (1/2)%Qp v)
   ∨ (∃ v, state ↦ #1 ∗ res ↦ SOMEV v ∗ FIN γ' v ∗ (Q v ∗ pending γ (1/2)%Qp ∨ shot γ v)))%I.
  Definition isTask (r: val) (γ γ': gname) (t: val) (P: val → iProp Σ) (Q: val → val → iProp Σ) : iProp Σ :=
    (∃ (arg : val) (state res : loc),
     ⌜t = (r, arg, #state, #res)%V⌝
     ∗ P arg ∗ INIT γ' (1/2)%Qp
     ∗ inv (N.@"task") (task_inv γ γ' state res (Q arg)))%I.
  Definition task (γ γ': gname) (t arg: val) (P: val → iProp Σ) (Q: val → val → iProp Σ) : iProp Σ :=
    (∃ (r: val) (state res : loc),
     ⌜t = (r, arg, #state, #res)%V⌝
     ∗ pending γ (1/2)%Qp
     ∗ inv (N.@"task") (task_inv γ γ' state res (Q arg)))%I.

  Ltac auto_equiv :=
    (* Deal with "pointwise_relation" *)
    repeat lazymatch goal with
           | |- pointwise_relation _ _ _ _ => intros ?
           end;
    (* Normalize away equalities. *)
    repeat match goal with
           | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
           | _ => progress simplify_eq
           end;
    (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
    try (f_equiv; fast_done || auto_equiv).

  Ltac solve_proper ::= solve_proper_core ltac:(fun _ => simpl; auto_equiv).

  Program Definition pre_runner (γ : name Σ b) (P: val → iProp Σ) (Q: val → val → iProp Σ) :
    (valO -n> iPropO Σ) -n> (valO -n> iPropO Σ) := λne R r,
    (∃ (body bag : val), ⌜r = (body, bag)%V⌝
     ∗ bagS b (N.@"bag") (λ x y, ∃ γ γ', isTask (body,x) γ γ' y P Q) γ bag
     ∗ ▷ ∀ r a: val, □ (R r ∗ P a -∗ WP body r a {{ v, Q a v }}))%I.
  Solve Obligations with solve_proper.

  Global Instance pre_runner_contractive (γ : name Σ b) P Q :
    Contractive (pre_runner γ P Q).
  Proof. unfold pre_runner. solve_contractive. Qed.

  Definition runner (γ: name Σ b) (P: val → iProp Σ) (Q: val → val → iProp Σ) :
    valO -n> iPropO Σ :=
    (fixpoint (pre_runner γ P Q))%I.

  Lemma runner_unfold γ r P Q :
    runner γ P Q r ≡
      (∃ (body bag : val), ⌜r = (body, bag)%V⌝
       ∗ bagS b (N.@"bag") (λ x y, ∃ γ γ', isTask (body,x) γ γ' y P Q) γ bag
       ∗ ▷ ∀ r a: val, □ (runner γ P Q r ∗ P a -∗ WP body r a {{ v, Q a v }}))%I.
  Proof. rewrite /runner. by rewrite {1}(fixpoint_unfold (pre_runner _ _ _) r). Qed.

  Global Instance runner_persistent γ r P Q :
    Persistent (runner γ P Q r).
  Proof. rewrite /runner (fixpoint_unfold (pre_runner _ _ _) r). apply _. Qed.

  Lemma newTask_spec γb (r a : val) P (Q : val → val → iProp Σ) :
    {{{ runner γb P Q r ∗ P a }}}
      newTask r a
    {{{ γ γ' t, RET t; isTask r γ γ' t P Q ∗ task γ γ' t a P Q }}}.
  Proof.
    iIntros (Φ) "[#Hrunner HP] HΦ".
    wp_rec. wp_pures.
    wp_alloc res as "Hres".
    wp_alloc status as "Hstatus".
    iMod (new_pending) as (γ) "[Htoken Htask]".
    iMod (new_INIT) as (γ') "[Hinit Hinit']".
    iMod (inv_alloc (N.@"task") _ (task_inv γ γ' status res (Q a))%I with "[-HP HΦ Htask Hinit]") as "#Hinv".
    { iNext. iLeft. iFrame. }
    wp_pures. iModIntro. iApply "HΦ".
    iFrame. iSplitL; iExists _,_,_; iFrame "Hinv"; eauto.
  Qed.

  Lemma task_Join_spec γb γ γ' (r t a : val) P Q :
    {{{ runner γb P Q r ∗ task γ γ' t a P Q }}}
       task_Join t
    {{{ res, RET res; Q a res }}}.
  Proof.
    iIntros (Φ) "[#Hrunner Htask] HΦ".
    iLöb as "IH".
    rewrite {2}/task_Join.
    iDestruct "Htask" as (r' state res) "(% & Htoken & #Htask)". simplify_eq.
    wp_rec. wp_pures.
    wp_bind (! #state)%E. iInv (N.@"task") as "Hstatus" "Hcl".
    rewrite {2}/task_inv.
    iDestruct "Hstatus" as "[>(Hstate & Hres)|[Hstatus|Hstatus]]".
    - wp_load.
      iMod ("Hcl" with "[Hstate Hres]") as "_".
      { iNext; iLeft; iFrame. }
      iModIntro. wp_op. wp_if.
      rewrite /task_Join. iApply ("IH" with "[$Htoken] HΦ").
      iExists _,_,_; iFrame "Htask"; eauto.
    - iDestruct "Hstatus" as (v) "(>Hstate & >Hres & HQ)".
      wp_load.
      iMod ("Hcl" with "[Hstate Hres HQ]") as "_".
      { iNext; iRight; iLeft. iExists _; iFrame. }
      iModIntro. wp_op. wp_if.
      rewrite /task_Join. iApply ("IH" with "[$Htoken] HΦ").
      iExists _,_,_; iFrame "Htask"; eauto.
    - iDestruct "Hstatus" as (v) "(>Hstate & >Hres & #HFIN & HQ)".
      wp_load.
      iDestruct "HQ" as "[[HQ Htoken2]|Hshot]"; last first.
      { iExFalso. iApply (shot_not_pending with "Hshot Htoken"). }
      iMod (shoot v γ with "[Htoken Htoken2]") as "#Hshot".
      { iApply (fractional_split_2 with "Htoken Htoken2").
        assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp.div_2.
        apply _. }
      iMod ("Hcl" with "[Hstate Hres]") as "_".
      { iNext. iRight. iRight. iExists _. iFrame. iFrame "HFIN".
        iRight. eauto. }
      iModIntro. wp_op. wp_if. wp_bind (!#res)%E.
      iInv (N.@"task") as "[>(Hstate & Hres & Hpending & HINIT)|[Hstatus|Hstatus]]" "Hcl".
      { iExFalso. iApply (shot_not_pending with "Hshot Hpending"). }
      { iDestruct "Hstatus" as (v') "(Hstate & Hres & Hpending & >HSETRES)".
        iExFalso. iApply (SET_RES_not_FIN with "HSETRES HFIN"). }
      iDestruct "Hstatus" as (v') "(Hstate & Hres & _ & HQ')".
      iDestruct "HQ'" as "[[? >Hpending]|>Hshot']".
      { iExFalso. iApply (shot_not_pending with "Hshot Hpending"). }
      iDestruct (shot_agree with "Hshot Hshot'") as %->.
      wp_load.
      iMod ("Hcl" with "[Hres Hstate]") as "_".
      { iNext. iRight. iRight. iExists _; iFrame. iFrame "HFIN". by iRight. }
      iModIntro. wp_match. iApply "HΦ"; eauto.
  Qed.

  Lemma task_Run_spec γb γ γ' r t P Q :
    {{{ runner γb P Q r ∗ isTask r γ γ' t P Q }}}
       task_Run t
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#Hrunner Htask] HΦ".
    rewrite runner_unfold.
    iDestruct "Hrunner" as (body bag) "(% & #Hbag & #Hbody)".
    iDestruct "Htask" as (arg state res) "(% & HP & HINIT & #Htask)".
    simplify_eq. rewrite /task_Run.
    wp_rec. wp_pures.
    wp_bind (body _ arg).
    iDestruct ("Hbody" $! (PairV body bag) arg) as "Hbody'".
    iSpecialize ("Hbody'" with "[HP]").
    { iFrame. rewrite runner_unfold.
      iExists _,_; iSplitR; eauto. }
    iApply (wp_wand with "Hbody'").
    iIntros (v) "HQ". wp_let.
    wp_bind (#res <- SOME v)%E. wp_inj.
    iInv (N.@"task") as "[>(Hstate & Hres & Hpending & HINIT')|[Hstatus|Hstatus]]" "Hcl".
    - wp_store.
      iMod (INIT_SET_RES v γ' with "[HINIT HINIT']") as "[HSETRES HSETRES']".
      { iApply (fractional_split_2 with "HINIT HINIT'").
        assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp.div_2.
        apply _. }
      iMod ("Hcl" with "[HSETRES Hstate Hres Hpending]") as "_".
      { iNext. iRight. iLeft. iExists _; iFrame. }
      iModIntro. wp_seq.
      iInv (N.@"task") as "[>(Hstate & Hres & Hpending & HINIT')|[Hstatus|Hstatus]]" "Hcl".
      { iExFalso. iApply (INIT_not_SET_RES with "HINIT' HSETRES'"). }
      + iDestruct "Hstatus" as (v') "(Hstate & Hres & Hpending & HSETRES)".
        wp_store.
        iDestruct (SET_RES_agree with "HSETRES HSETRES'") as %->.
        iMod (SET_RES_FIN v v with "[HSETRES HSETRES']") as "#HFIN".
        { iApply (fractional_split_2 with "HSETRES HSETRES'").
          assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp.div_2.
          apply _. }
        iMod ("Hcl" with "[-HΦ]") as "_".
        { iNext. do 2 iRight. iExists _; iFrame. iFrame "HFIN". iLeft. iFrame.  }
        iModIntro. by iApply "HΦ".
      + iDestruct "Hstatus" as (v') "(Hstate & Hres & >HFIN & HQ')".
        iExFalso. iApply (SET_RES_not_FIN with "HSETRES' HFIN").
    - iDestruct "Hstatus" as (v') "(Hstate & Hres & Hpending & >HSETRES)".
      iExFalso. iApply (INIT_not_SET_RES with "HINIT HSETRES").
    - iDestruct "Hstatus" as (v') "(Hstate & Hres & >HFIN & HQ')".
      iExFalso. iApply (INIT_not_FIN with "HINIT HFIN").
  Qed.

  Lemma runner_runTask_spec γb P Q r:
    {{{ runner γb P Q r }}}
      runner_runTask r
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "#Hrunner HΦ".
    rewrite runner_unfold /runner_runTask.
    iDestruct "Hrunner" as (body bag) "(% & #Hbag & #Hbody)"; simplify_eq.
    wp_rec. wp_pures.
    wp_bind (popBag b _).
    iApply (popBag_spec with "Hbag").
    iNext. iIntros (t') "[_ [%|Ht]]"; simplify_eq.
    - wp_match. by iApply "HΦ".
    - iDestruct "Ht" as (t) "[% Ht]".
      iDestruct "Ht" as (γ γ') "Htask".
      simplify_eq. wp_match.
      iApply (task_Run_spec with "[Hbag Hbody Htask]"); last done.
      iFrame "Htask". rewrite runner_unfold.
      iExists _,_; iSplit; eauto.
  Qed.

  Lemma runner_runTasks_spec γb P Q r:
    {{{ runner γb P Q r }}}
      runner_runTasks r
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "#Hrunner HΦ".
    iLöb as "IH". rewrite /runner_runTasks.
    wp_rec. wp_bind (runner_runTask r).
    iApply runner_runTask_spec; eauto.
    iNext. iIntros "_". wp_seq. by iApply "IH".
  Qed.

  Lemma loop_spec (n i : nat) P Q γb r:
    {{{ runner γb P Q r }}}
      (RecV "loop" "i" (
         if: "i" < #n
         then Fork (runner_runTasks r);; "loop" ("i" + #1)
         else r)) #i
    {{{ r, RET r; runner γb P Q r }}}.
  Proof.
    iIntros (Φ) "#Hrunner HΦ".
    iLöb as "IH" forall (i).
    wp_rec. wp_op. case_bool_decide; wp_if; last first.
    { by iApply "HΦ". }
    wp_bind (Fork _). iApply (wp_fork with "[]").
    - iNext. by iApply runner_runTasks_spec.
    - iNext. wp_seq. wp_op.
      (* Set Printing Coercions. *)
      assert ((Z.of_nat i + 1)%Z = Z.of_nat (i + 1)) as -> by lia.
      iApply ("IH" with "HΦ").
  Qed.

  Lemma newRunner_spec P Q (f : val) (n : nat) :
    {{{ ∀ (γ: name Σ b) (r: val),
          □ ∀ a: val, (runner γ P Q r ∗ P a -∗ WP f r a {{ v, Q a v }}) }}}
       newRunner f #n
    {{{ γb r, RET r; runner γb P Q r }}}.
  Proof.
    iIntros (Φ) "#Hf HΦ".
    unfold newRunner.
    wp_lam. wp_pures.
    wp_bind (newBag b #()).
    iApply (newBag_spec b (N.@"bag") (λ x y, ∃ γ γ', isTask (f,x) γ γ' y P Q)%I); auto.
    iNext. iIntros (bag). iDestruct 1 as (γb) "#Hbag".
    wp_let. wp_pair. wp_let. wp_closure. wp_let.
    iAssert (runner γb P Q (PairV f bag))%I with "[]" as "#Hrunner".
    { rewrite runner_unfold. iExists _,_. iSplit; eauto. }
    iApply (loop_spec n 0 with "Hrunner [HΦ]"); eauto.
  Qed.

  Lemma runner_Fork_spec γb (r a:val) P Q :
    {{{ runner γb P Q r ∗ P a }}}
       runner_Fork r a
    {{{ γ γ' t, RET t; task γ γ' t a P Q }}}.
  Proof.
    iIntros (Φ) "[#Hrunner HP] HΦ".
    rewrite /runner_Fork runner_unfold.
    iDestruct "Hrunner" as (body bag) "(% & #Hbag & #Hbody)". simplify_eq.
    Local Opaque newTask.
    wp_lam. wp_pures. wp_bind (newTask _ _).
    iApply (newTask_spec γb (body,bag) a P Q with "[Hbag Hbody HP]").
    { iFrame "HP". rewrite runner_unfold.
      iExists _,_; iSplit; eauto. }
    iNext. iIntros (γ γ' t) "[Htask Htask']". wp_let.
    wp_bind (pushBag _ _ _).
    iApply (pushBag_spec with "[$Hbag Htask]"); eauto.
    iNext. iIntros "_". wp_seq. by iApply "HΦ".
  Qed.
End contents.

Global Opaque runner task newRunner runner_Fork task_Join.
