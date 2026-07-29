(** Concurrent Runner example from
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

Fibonaci divide-and-conquer computation
*)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import cmra agree frac csum excl.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris_examples.hocap Require Import abstract_bag shared_bag concurrent_runners.

Section contents.
  Context `{heapGS Σ, !oneshotG Σ, !saG Σ}.
  Variable b : bag Σ.
  Variable N : namespace.

  Fixpoint fib (a : nat) : nat :=
    match a with
    | O => 1
    | S n =>
      match n with
      | O => 1
      | S n' => fib n + fib n'
      end
    end.
  Local Arguments fib !_ / : simpl nomatch.

  Definition seqFib : val := rec: "fib" "a" :=
    if: "a" = #0
    then #1
    else if: "a" = #1
         then #1
         else ("fib" ("a"-#1)) + ("fib" ("a"-#2)).

  Lemma seqFib_spec (n : nat) :
    {{{ True }}} seqFib #n {{{ (m : nat), RET #m; ⌜fib n = m⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH" forall (n Φ).
    wp_rec. simpl. wp_op. case_bool_decide; simplify_eq; wp_if.
    { assert (n = O) as -> by lia.
      by iApply ("HΦ" $! 1). }
    wp_op. case_bool_decide; simplify_eq; wp_if.
    { assert (n = 1) as -> by lia.
      by iApply ("HΦ" $! 1). }
    wp_op. destruct n as [|[|n]]=> //.
    rewrite !Nat2Z.inj_succ.
    replace (Z.succ (Z.succ n) - 2)%Z with (Z.of_nat n) by lia.
    wp_apply "IH". iIntros (? <-).
    wp_op.
    replace (Z.succ (Z.succ n) - 1)%Z with (Z.of_nat (S n)) by lia.
    wp_apply "IH". iIntros (? <-). wp_op.
    rewrite -Nat2Z.inj_add. by iApply "HΦ".
  Qed.

  Definition parFib : val := λ: "r" "a",
    if: "a" < #25 then seqFib "a"
    else let: "a1" := "a" - #1 in
         let: "a2" := "a" - #2 in
         let: "t1" := runner_Fork b "r" "a1" in
         let: "t2" := runner_Fork b "r" "a2" in
         (task_Join "t1") + (task_Join "t2").

  Definition fibRunner : val := λ: "n" "a",
    let: "r" := newRunner b parFib "n" in
    task_Join (runner_Fork b "r" "a").

  Definition P (v: val) : iProp Σ := (∃ n: nat, ⌜v = #n⌝)%I.
  Definition Q (a v: val) : iProp Σ := (∃ n: nat, ⌜a = #n⌝ ∧ ⌜v = #(fib n)⌝)%I.
  Lemma parFib_spec r γb a :
    {{{ runner b N γb P Q r ∗ P a }}}
      parFib r a
    {{{ v, RET v; Q a v }}}.
  Proof.
    iIntros (Φ) "[#Hrunner HP] HΦ".
    iDestruct "HP" as (n) "%"; simplify_eq.
    wp_lam. wp_let. wp_op. case_bool_decide; wp_if.
    - iApply seqFib_spec; eauto.
      iNext. iIntros (? <-). iApply "HΦ".
      iExists n; done.
    - do 2 (wp_op; wp_let).
      destruct n as [|[|n]]=> //.
      rewrite !Nat2Z.inj_succ.
      replace (Z.succ (Z.succ n) - 2)%Z with (Z.of_nat n) by lia.
      replace (Z.succ (Z.succ n) - 1)%Z with (Z.succ n) by lia.
      wp_apply (runner_Fork_spec).
      { iFrame "Hrunner". iExists (S n). by rewrite Nat2Z.inj_succ. }
      iIntros (γ1 γ1' t1) "Ht1". wp_let.
      wp_apply (runner_Fork_spec).
      { iFrame "Hrunner". eauto. }
      iIntros (γ2 γ2' t2) "Ht2". wp_let.
      wp_apply (task_Join_spec with "[$Ht2]"); try done.
      iIntros (v2) "HQ"; simplify_eq.
      iDestruct "HQ" as (m2' m2) "%". simplify_eq.
      wp_apply (task_Join_spec with "[$Ht1]"); try done.
      iIntros (v1) "HQ"; simplify_eq.
      iDestruct "HQ" as (m1' m1) "%". simplify_eq.
      wp_op. iApply "HΦ". iExists (S (S m2')).
      rewrite !Nat2Z.inj_succ -Nat2Z.inj_add.
      by replace m1' with (S m2') by lia.
  Qed.

  Lemma fibRunner_spec (n a : nat) :
    {{{ True }}} fibRunner #n #a {{{ (m : nat), RET #m; ⌜fib a = m⌝ }}}.
  Proof using Type* N.
    iIntros (Φ) "_ HΦ".
    unfold fibRunner. wp_lam. wp_let. wp_bind (newRunner _ _ _).
    iApply (newRunner_spec b N P Q).
    - iIntros (γb r). iModIntro. iIntros (a') "[#Hrunner HP]".
      iApply (parFib_spec with "[$HP]"); eauto.
    - iNext. iIntros (γb r) "#Hrunner".
      wp_let. wp_bind (runner_Fork b r #a).
      iApply (runner_Fork_spec); eauto.
      iNext. iIntros (γ γ' t) "Ht".
      iApply (task_Join_spec with "[$Ht]"); eauto.
      iNext. iIntros (res). iDestruct 1 as (?) "[% %]"; simplify_eq/=.
      by iApply "HΦ".
  Qed.
End contents.
