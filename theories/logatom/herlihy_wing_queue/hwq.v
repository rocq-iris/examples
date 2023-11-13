From iris.algebra Require Import numbers excl auth list gset gmap agree csum.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export invariants proph_map saved_prop.
From iris.program_logic Require Export atomic.
From iris.heap_lang.lib Require Import arith diverge.
From iris.heap_lang Require Import proofmode notation par.
From iris_examples.logatom.herlihy_wing_queue Require Import spec.
From iris.prelude Require Import options.

(** * Some array-related notations ******************************************)

Notation "new_array: sz" :=
  (AllocN sz%E NONEV) (at level 80) : expr_scope.

Notation "e1 <[[ e2 ]]>" :=
  (BinOp OffsetOp e1%E e2%E) (at level 8) : expr_scope.

(** * Implementation of the queue operations ********************************)

(** new_queue(sz){
      let ar := new_array sz None in
      let back := ref 0 in
      let p := new_proph () in
      {sz, ar, back, p}
    } *)
Definition new_queue : val :=
  λ: "sz",
    let: "ar" := new_array: "sz" in
    let: "back" := ref #0 in (* First free cell. *)
    let: "p" := NewProph in
    ("sz", "ar", "back", "p").

(** enqueue(q : queue, x : item){
      let i : int := FAA(q.back, 1) in
      if(i < q.size){
        q.items[i] := x
      } else {
        while true;
      }
    } *)
Definition enqueue : val :=
  λ: "q" "x",
    let: "q_size" := Fst (Fst (Fst "q")) in
    let: "q_ar"   := Snd (Fst (Fst "q")) in
    let: "q_back" := Snd (Fst "q") in
    (* Get the next free index. *)
    let: "i" := FAA "q_back" #1 in
    (* Check not full, and actually insert. *)
    if: "i" < "q_size" then "q_ar"<[["i"]]> <- SOME "x" ;; Skip
    else diverge #().

(** dequeue(q : queue){
      let range = min(!q.back, q.size) in
      let rec dequeue_aux(i) =
        if i = 0 {
          dequeue(q)
        } else {
          let j = range - i in
          let x = ! q.ar[j] in
          if x == null {
            dequeue_aux(i-1)
          } else {
            if resolve (CAS q.ar[j] x null) q.p (j, x) {
              v
            } else {
              dequeue_aux(i-1)
            }
          }
        }
      in
      dequeue_aux(range)
    } *)
Definition dequeue_aux : val :=
  rec: "loop" "dequeue" "q" "range" "i" :=
    if: "i" = #0 then "dequeue" "q" else
      let: "q_ar" := Snd (Fst (Fst "q")) in
      let: "q_p"  := Snd "q" in
      let: "j"    := "range" - "i" in
      let: "x"    := ! "q_ar"<[["j"]]> in
      match: "x" with
        NONE     => "loop" "dequeue" "q" "range" ("i" - #1)
      | SOME "v" =>
        let: "c" := Resolve (CmpXchg ("q_ar"<[["j"]]>) "x" NONE) "q_p" "j" in
        if: Snd "c" then "v" else "loop" "dequeue" "q" "range" ("i" - #1)
      end.
Definition dequeue : val :=
  rec: "dequeue" "q" :=
    let: "q_size" := Fst (Fst (Fst "q")) in
    let: "q_back" := Snd (Fst "q") in
    let: "range"  := minimum !"q_back" "q_size" in
    dequeue_aux "dequeue" "q" "range" "range".

(** * Definition of the cameras we need for queues **************************)

Definition prod4R A B C D E :=
  prodR (prodR (prodR (prodR A B) C) D) E.

Definition oneshotUR := optionUR $ csumR (exclR unitR) (agreeR unitR).
Definition shot     : oneshotUR := Some $ Cinr $ to_agree ().
Definition not_shot : oneshotUR := Some $ Cinl $ Excl ().

Definition per_slot :=
  prod4R
    (* Unique token for the index. *)
    (optionUR $ exclR unitR)
    (* The location stored at our index, which always remains the same. *)
    (optionUR $ agreeR locO)
    (* Possible unique name for the index, only if being helped. *)
    (optionUR $ exclR gnameO)
    (* One shot witnessing the transition from pending to helped. *)
    oneshotUR
    (* One shot witnessing the physical writing of the value in the slot. *)
    oneshotUR.

Definition eltsUR := authR $ optionUR $ exclR $ listO locO.
Definition contUR := csumR (exclR unitR) (agreeR (prodO natO natO)).
Definition slotUR := authR $ gmapUR nat per_slot.
Definition backUR := authR max_natUR.

Class hwqG Σ :=
  HwqG {
    hwq_arG   :: inG Σ eltsUR; (** Logical contents of the queue. *)
    hwq_contG :: inG Σ contUR; (** One-shot for contradiction states. *)
    hwq_slotG :: inG Σ slotUR; (** State data for used array slots. *)
    hwq_back  :: inG Σ backUR; (** Used to show that back only increases. *)
  }.

Definition hwqΣ : gFunctors :=
  #[GFunctor eltsUR; GFunctor contUR; GFunctor slotUR; GFunctor backUR].

Global Instance subG_hwqΣ {Σ} : subG hwqΣ Σ → hwqG Σ.
Proof. solve_inG. Qed.

(** * The specifiaction... **************************************************)

Section herlihy_wing_queue.

Context `{!heapGS Σ, !savedPropG Σ, !hwqG Σ}.
Context (N : namespace).
Notation iProp := (iProp Σ).
Implicit Types γe γc γs : gname.
Implicit Types sz : nat.
Implicit Types ℓ_ar ℓ_back : loc.
Implicit Types p : proph_id.
Implicit Types v : val.
Implicit Types pvs : list nat.

(** Operations for the CMRA representing the logical contents of the queue. *)

Lemma new_elts l : ⊢ |==> ∃ γe, own γe (● Excl' l) ∗ own γe (◯ Excl' l).
Proof.
  iMod (own_alloc (● Excl' l ⋅ ◯ Excl' l)) as (γe) "[H● H◯]".
  - by apply auth_both_valid_discrete.
  - iModIntro. iExists γe. iFrame.
Qed.

Lemma sync_elts γe (l1 l2 : list loc) :
  own γe (● Excl' l1) -∗ own γe (◯ Excl' l2) -∗ ⌜l1 = l2⌝.
Proof.
  iIntros "H● H◯". iCombine "H●" "H◯" as "H".
  iDestruct (own_valid with "H") as "H".
  by iDestruct "H" as %[H%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
Qed.

Lemma update_elts γe (l1 l2 l : list loc) :
  own γe (● Excl' l1) -∗ own γe (◯ Excl' l2) ==∗
    own γe (● Excl' l) ∗ own γe (◯ Excl' l).
Proof.
  iIntros "H● H◯". iCombine "H●" "H◯" as "H". rewrite -own_op.
  iApply (own_update with "H").
  by apply auth_update, option_local_update, exclusive_local_update.
Qed.

(* Fragmental part, made available during atomic updates. *)
Definition hwq_cont γe (elts : list loc) : iProp :=
  own γe (◯ Excl' elts).

Lemma hwq_cont_exclusive γe elts1 elts2 :
  hwq_cont γe elts1 -∗ hwq_cont γe elts2 -∗ False.
Proof.
  iIntros "H1 H2".
  by iCombine "H1 H2" gives %?%auth_frag_op_valid_1.
Qed.

(** Operations for the CMRA used to show that back only increases. *)

Definition back_value γb n := own γb (● MaxNat n).
Definition back_lower_bound γb n := own γb (◯ MaxNat n).

Lemma new_back : ⊢ |==> ∃ γb, back_value γb 0.
Proof.
  iMod (own_alloc (● MaxNat 0)) as (γb) "H●".
  - by rewrite auth_auth_valid.
  - by iExists γb.
Qed.

Lemma back_incr γb n :
  back_value γb n ==∗ back_value γb (S n).
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ _]"; last done.
  apply auth_update_alloc, (max_nat_local_update _ _ (MaxNat (S n))). simpl. lia.
Qed.

Lemma back_snapshot γb n :
  back_value γb n ==∗ back_value γb n ∗ back_lower_bound γb n.
Proof.
  iIntros "H●". rewrite -own_op. iApply (own_update with "H●").
  by apply auth_update_alloc, max_nat_local_update.
Qed.

Lemma back_le γb n1 n2 :
  back_value γb n1 -∗ back_lower_bound γb n2 -∗ ⌜n2 ≤ n1⌝.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Hvalid. iPureIntro.
  apply auth_both_valid_discrete in Hvalid as [H1%max_nat_included _]. done.
Qed.

(* Stores a lower bound on the [i2] part of any contradiction that
   has arised or may arise in the future. *)
Definition i2_lower_bound γi n := back_value γi n.

(* Witness that the [i2] part of any (future or not) contradicton is
   greater than [n]. *)
Definition no_contra_wit γi n := back_lower_bound γi n.

Lemma i2_lower_bound_update γi n m :
  n ≤ m →
  i2_lower_bound γi n ==∗ i2_lower_bound γi m.
Proof.
  iIntros (H) "H●". iMod (own_update with "H●") as "[$ _]"; last done.
  apply auth_update_alloc, (max_nat_local_update _ _ (MaxNat m)). simpl. lia.
Qed.

Lemma i2_lower_bound_snapshot γi n :
  i2_lower_bound γi n ==∗ i2_lower_bound γi n ∗ no_contra_wit γi n.
Proof.
  iIntros "H●". rewrite -own_op. iApply (own_update with "H●").
  by apply auth_update_alloc, max_nat_local_update.
Qed.

(** Operations for the one-shot CMRA used for contradiction states. *)

(** Element for "no contradiction yet". *)
Definition no_contra γc :=
  own γc (Cinl (Excl ())).

(** Element witnessing a contradiction [(i1, i2)]. *)
Definition contra γc (i1 i2 : nat) :=
  own γc (Cinr (to_agree (i1, i2))).

Lemma new_no_contra : ⊢ |==> ∃ γc, no_contra γc.
Proof. by apply own_alloc. Qed.

Lemma to_contra i1 i2 γc : no_contra γc ==∗ contra γc i1 i2.
Proof. apply bi.entails_wand, own_update. by apply cmra_update_exclusive. Qed.

Lemma contra_not_no_contra i1 i2 γc :
  no_contra γc -∗ contra γc i1 i2 -∗ False.
Proof. iIntros "HnoC HC". iCombine "HnoC HC" gives %[]. Qed.

Lemma contra_agree i1 i2 i1' i2' γc :
  contra γc i1 i2 -∗ contra γc i1' i2' -∗ ⌜i1' = i1 ∧ i2' = i2⌝.
Proof.
  iIntros "HC HC'". iCombine "HC HC'" gives %H.
  iPureIntro. apply to_agree_op_inv_L in H. by inversion H.
Qed.

Global Instance contra_persistent γc i1 i2 : Persistent (contra γc i1 i2).
Proof. apply own_core_persistent. by rewrite /CoreId. Qed.

(** Operations for the state data. *)

Inductive state :=
  (** Help was requested (element not committed). *)
  | Pend : gname → state
  (** Help has been provided (element committed). *)
  | Help : gname → state
  (** The enqueue operation known it has been committed. *)
  | Done :         state.

Local Instance state_inhabited : Inhabited state.
Proof. constructor. refine Done. Qed.

(** Data associated to each slot. The four components are:
     - the location that is being written in the slot,
     - a possible name for a stored proposition containing the postcondition
       of the atomic update of the enqueue happening for the slot (used only
       in case of helping),
     - state of the slot,
     - [true] if a value was physically written in the slot. *)
Definition slot_data : Type := loc * state * bool.

Implicit Types slots : gmap nat slot_data.

Definition update_slot i f slots :=
  match slots !! i with
  | Some d => <[i := f d]> (delete i slots)
  | None   => slots
  end.

Definition val_of (data : slot_data) : loc :=
  match data with (l, _, _) => l end.

Definition state_of (data : slot_data) : state :=
  match data with (_, s, _) => s end.

Definition name_of (data : slot_data) : option gname :=
  match state_of data with Pend γ => Some γ | Help γ => Some γ | _ => None end.

Definition was_written (data : slot_data) : bool :=
  match data with (_, _, b) => b end.

Definition was_committed (data : slot_data) : bool :=
  match state_of data with Pend _ => false | _ => true end.

Definition set_written (data : slot_data) : slot_data :=
  match data with (l, s, _) => (l, s, true) end.

Definition set_written_and_done (data : slot_data) : slot_data :=
  match data with (l, _, _) => (l, Done, true) end.

Definition to_helped (γ : gname) (data : slot_data) : slot_data :=
  match data with (l, _, w) => (l, Help γ, w) end.

Definition to_done (data : slot_data) : slot_data :=
  match data with (l, _, w) => (l, Done, w) end.

Definition physical_value (data : slot_data) : val :=
  match data with (l, _, w) => if w then SOMEV #l else NONEV end.

Lemma val_of_set_written d : val_of (set_written d) = val_of d.
Proof. by destruct d as [[l s] w]. Qed.

Lemma was_written_set_written d : was_written (set_written d) = true.
Proof. by destruct d as [[l s] w]. Qed.

Lemma state_of_set_written d : state_of (set_written d) = state_of d.
Proof. by destruct d as [[l s] w]. Qed.

Definition of_slot_data (data : slot_data) : per_slot :=
  match data with
  | (l, s, w) =>
    let name := match s with Pend γ => Excl' γ | Help γ => Excl' γ | Done => None end in
    let comm := if was_committed data then shot else not_shot in
    let wr := if w then shot else not_shot in
    (Excl' (), Some (to_agree l), name, comm, wr)
  end.

Lemma of_slot_data_valid d : ✓ of_slot_data d.
Proof. by destruct d as [[l []] []]. Qed.

(* The (unique) token for slot [i]. *)
Definition slot_token γs i :=
  own γs (◯ {[i := (Excl' (), None, None, None, None)]} : slotUR).

(* A witness that the location enqueued in slot [i] is [l]. *)
Definition slot_val_wit γs i l :=
  own γs (◯ {[i := (None, Some (to_agree l), None, None, None)]} : slotUR).

(* A witness that the element inserted at slot [i] has been committed. *)
Definition slot_committed_wit γs i :=
  own γs (◯ {[i := (None, None, None, shot, None)]} : slotUR).

Definition slot_name_tok γs i γ :=
  own γs (◯ {[i := (None, None, Excl' γ, None, None)]} : slotUR).

(* A witness that the element inserted at slot [i] has been written. *)
Definition slot_written_wit γs i :=
  own γs (◯ {[i := (None, None, None, None, shot)]} : slotUR).

(* A token proving that the enqueue in slot [i] has not been commited. *)
Definition slot_pending_tok γs i :=
  own γs (◯ {[i := (None, None, None, not_shot, None)]} : slotUR).

(* A token proving that no value has been written in slot [i]. *)
Definition slot_writing_tok γs i :=
  own γs (◯ {[i := (None, None, None, None, not_shot)]} : slotUR).

(* Initial slot data, with not allocated slots. *)
Lemma new_slots : ⊢ |==> ∃ γs, own γs (● ∅).
Proof.
  iMod (own_alloc (● ∅ ⋅ ◯ ∅)) as (γs) "[H● _]".
  - by apply auth_both_valid_discrete.
  - iModIntro. iExists γs. iFrame.
Qed.

(* Allocate a new slot with data [d] at the fresh index [i]. *)
Lemma alloc_slot γs slots (i : nat) (d : slot_data) :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> (<[i := d]> slots)) : slotUR) ∗
    own γs (◯ {[i := of_slot_data d]} : slotUR).
Proof.
  iIntros (Hi) "H". rewrite -own_op fmap_insert.
  iApply (own_update with "H"). apply auth_update_alloc.
  apply alloc_singleton_local_update.
  - by rewrite lookup_fmap Hi.
  - apply of_slot_data_valid.
Qed.

Lemma alloc_done_slot γs slots i l :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> (<[i := (l, Done, false)]> slots)) : slotUR) ∗
    slot_token γs i ∗
    slot_val_wit γs i l ∗
    slot_committed_wit γs i ∗
    slot_writing_tok γs i.
Proof.
  iIntros (Hi) "H". iMod (alloc_slot _ _ _ _ Hi with "H") as "[$ Hi]".
  repeat rewrite -own_op. repeat rewrite -auth_frag_op.
  repeat rewrite -insert_op. repeat rewrite left_id.
  by rewrite insert_empty.
Qed.

Lemma alloc_pend_slot γs slots i l γ :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> (<[i := (l, Pend γ, false)]> slots)) : slotUR) ∗
    slot_token γs i ∗
    slot_val_wit γs i l ∗
    slot_pending_tok γs i ∗
    slot_name_tok γs i γ ∗
    slot_writing_tok γs i.
Proof.
  iIntros (Hi) "H". iMod (alloc_slot _ _ _ _ Hi with "H") as "[$ Hi]".
  repeat rewrite -own_op. repeat rewrite -auth_frag_op.
  repeat rewrite -insert_op. repeat rewrite left_id.
  by rewrite insert_empty.
Qed.

Lemma use_val_wit γs slots i l :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_val_wit γs i l -∗
  ⌜val_of <$> slots !! i = Some l⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %H.
  iPureIntro. apply auth_both_valid_discrete in H as [H%singleton_included_l _].
  destruct H as [ps (H1 & H2%option_included)]. rewrite lookup_fmap in H1.
  destruct (slots !! i) as [d|]; last by inversion H1. simpl in H1.
  inversion_clear H1.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into H1 end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct H1 as [[[[_ H1] _] _] _]; simpl in H1. simpl. f_equal.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ H2] _] _] _]; simpl in H2.
    assert (Some (to_agree l) ≡ Some (to_agree dl)) as H by by transitivity b2.
    apply Some_equiv_inj, to_agree_inj in H. done.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    assert (Some (to_agree l) ≼ Some (to_agree dl)) as H by set_solver.
    apply option_included in H.
    destruct H as [H|[a [b (H11 & H12 & H13)]]]; first done.
    simplify_eq. destruct H13 as [H|H].
    + by apply to_agree_inj in H.
    + by apply to_agree_included in H.
Qed.

Lemma use_name_tok γs slots i γ :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ -∗
  ⌜name_of <$> slots !! i = Some (Some γ)⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %H.
  iPureIntro. apply auth_both_valid_discrete in H as [H%singleton_included_l _].
  destruct H as [ps (H1 & H2%option_included)]. rewrite lookup_fmap in H1.
  destruct (slots !! i) as [d|]; last by inversion H1. simpl in H1.
  inversion_clear H1.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into H1 end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct H1 as [[[[_ _] H1] _] _]; simpl in H1. simpl. f_equal.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] H2] _] _]; simpl in H2.
    destruct ds as [γ'|γ'|]; rewrite /name_of /=; try f_equal.
    + assert (Excl' γ ≡ Excl' γ') as H by by transitivity b3.
      inversion H as [x y HH|]. by inversion HH.
    + assert (Excl' γ ≡ Excl' γ') as H by by transitivity b3.
      inversion H as [x y HH|]. by inversion HH.
    + assert (Excl' γ ≡ None) as H by by transitivity b3.
      inversion H.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    destruct ds as [γ'|γ'|]; rewrite /name_of /=; try f_equal.
    + assert (Excl' γ ≼ Excl' γ') as H by set_solver.
      by apply Excl_included in H.
    + assert (Excl' γ ≼ Excl' γ') as H by set_solver.
      by apply Excl_included in H.
    + assert (Excl' γ ≼ None) as H by set_solver.
      exfalso. apply option_included in H as [H|H]; first done.
      destruct H as [a [b (H11 & H12 & H13)]]. by simplify_eq.
Qed.

Lemma shot_not_equiv_not_shot : shot ≢ not_shot.
Proof.
  intros H. rewrite /shot /not_shot in H.
  inversion H as [x y HAbsurd|]. inversion HAbsurd.
Qed.

Lemma shot_not_equiv_not_shot' e : shot ≢ not_shot ⋅ e.
Proof.
  intros H. rewrite /shot /not_shot in H.
  destruct e as [e|]; first destruct e.
  - rewrite -Some_op -Cinl_op in H.
    inversion H as [x y Habsurd|]; inversion Habsurd.
  - rewrite -Some_op in H. compute in H.
    inversion H as [x y HAbsurd|]. inversion HAbsurd.
  - inversion H as [x y HAbsurd|]. inversion HAbsurd.
  - inversion H as [x y HAbsurd|]. inversion HAbsurd.
Qed.

Lemma shot_not_included_not_shot : ¬ shot ≼ not_shot.
Proof.
  intros H. rewrite /shot /not_shot in H.
  apply option_included in H. destruct H as [H|H]; first done.
  destruct H as [a [b (H1 & H2 & [H3|H3])]].
  - simplify_eq. by inversion H3.
  - simplify_eq. apply csum_included in H3.
    destruct H3 as [H3|H3]; first done. destruct H3 as [H3|H3].
    + destruct H3 as [a [b (H1 & H2 & H3)]]. by inversion H1.
    + destruct H3 as [a [b (H1 & H2 & H3)]]. by inversion H1.
Qed.

Lemma use_committed_wit γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_committed_wit γs i -∗
  ⌜was_committed <$> slots !! i = Some true⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %H.
  iPureIntro. apply auth_both_valid_discrete in H as [H%singleton_included_l _].
  destruct H as [ps (H1 & H2%option_included)]. rewrite lookup_fmap in H1.
  destruct (slots !! i) as [d|]; last by inversion H1. simpl in H1.
  inversion_clear H1.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into H1 end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct H1 as [[[[_ _] _] H1]]; simpl in H1. f_equal.
  destruct (was_committed (dl, ds, dw)); first done. exfalso.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] _] H2] _]; simpl in H2.
    apply shot_not_equiv_not_shot. set_solver.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    apply shot_not_included_not_shot. set_solver.
Qed.

Lemma use_written_wit γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_written_wit γs i -∗
  ⌜was_written <$> slots !! i = Some true⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %H.
  iPureIntro. apply auth_both_valid_discrete in H as [H%singleton_included_l _].
  destruct H as [ps (H1 & H2%option_included)]. rewrite lookup_fmap in H1.
  destruct (slots !! i) as [d|]; last by inversion H1. simpl in H1.
  inversion_clear H1.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into H1 end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5]. destruct d as [[dl ds] dw].
  destruct H1 as [[[[_ _] _] _] H1]; simpl in H1. f_equal.
  destruct dw; first done. exfalso.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] _] _] H2]; simpl in H2.
    exfalso. apply shot_not_equiv_not_shot. set_solver.
  - apply prod_included in H2 as [_ H2]; simpl in H2.
    exfalso. apply shot_not_included_not_shot. set_solver.
Qed.

Lemma use_writing_tok γs i slots :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_writing_tok γs i ==∗
    own γs (● (of_slot_data <$> update_slot i set_written slots) : slotUR) ∗
    slot_written_wit γs i.
Proof.
  iIntros "Hs● Htok". iCombine "Hs● Htok" as "H". rewrite -own_op.
  iDestruct (own_valid with "H") as %Hvalid.
  iApply (own_update with "H").
  apply auth_both_valid_discrete in Hvalid as [H1 H2].
  apply singleton_included_l in H1 as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|] eqn:Hi; last by inversion H1_1.
  apply Some_equiv_inj in H1_1.
  assert (w = false) as ->.
  { destruct w; [ exfalso | done ].
    apply Some_included in H1_2 as [H1_2|H1_2].
    - assert ((None, None, None, None, not_shot)
            ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
      destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
      by apply shot_not_equiv_not_shot.
    - destruct H1_2 as [f H1_2].
      assert ((None, None, None, None, not_shot) ⋅ f
            ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
      destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
      by eapply shot_not_equiv_not_shot'. }
  rewrite /update_slot Hi insert_delete_insert fmap_insert.
  apply auth_update. eapply (singleton_local_update _ i).
  { by rewrite lookup_fmap Hi. }
  rewrite /set_written. apply prod_local_update; first done. simpl.
  by apply option_local_update, exclusive_local_update.
Qed.

Lemma writing_tok_not_written γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_writing_tok γs i -∗
    ⌜was_written <$> slots !! i = Some false⌝.
Proof.
  iIntros "Hs● Htok". iCombine "Hs● Htok" as "H".
  iDestruct (own_valid with "H") as %Hvalid%auth_both_valid_discrete.
  iPureIntro. destruct Hvalid as [H1 H2].
  apply singleton_included_l in H1 as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|]; last by inversion H1_1.
  apply Some_equiv_inj in H1_1. simpl. f_equal. destruct w; last done.
  exfalso. apply Some_included in H1_2 as [H1_2|H1_2].
  - assert ((None, None, None, None, not_shot)
          ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
    destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
    by apply shot_not_equiv_not_shot.
  - destruct H1_2 as [f H1_2].
    assert ((None, None, None, None, not_shot) ⋅ f
          ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
    destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
    by eapply shot_not_equiv_not_shot'.
Qed.

Lemma None_op {A : cmra} : (None : optionUR A) ⋅ None = None.
Proof. done. Qed.

Lemma use_pending_tok γs i γ slots :
  state_of <$> slots !! i = Some (Pend γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_pending_tok γs i ==∗
    own γs (● (of_slot_data <$> update_slot i (to_helped γ) slots) : slotUR) ∗
    slot_committed_wit γs i.
Proof.
  iIntros (Hlookup) "Hs● Htok". iCombine "Hs● Htok" as "H".
  rewrite -own_op. iDestruct (own_valid with "H") as %Hvalid.
  iApply (own_update with "H").
  apply auth_both_valid_discrete in Hvalid as [H1 H2].
  apply singleton_included_l in H1 as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|] eqn:Hi; last by inversion H1_1.
  simpl in Hlookup. inversion Hlookup; subst s.
  rewrite /update_slot Hi insert_delete_insert fmap_insert.
  apply auth_update. repeat rewrite pair_op.
  eapply (singleton_local_update _ i). { by rewrite lookup_fmap Hi. }
  rewrite /to_helped. repeat rewrite None_op.
  repeat apply prod_local_update; try done.
  by apply option_local_update, exclusive_local_update.
Qed.

Lemma slot_token_exclusive γs i :
  slot_token γs i -∗ slot_token γs i -∗ False.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %H. iPureIntro.
  move:H =>/auth_frag_valid H. apply singleton_valid in H.
  by repeat apply pair_valid in H as [H _]; simpl in H.
Qed.

Lemma helped_to_done_aux γs i γ slots :
  state_of <$> slots !! i = Some (Help γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ ==∗
    own γs (● (of_slot_data <$> update_slot i to_done slots) : slotUR) ∗
    own γs (◯ {[i := (None, None, None, None, None)]} : slotUR).
Proof.
  iIntros (H) "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Hvalid. rewrite -own_op.
  iApply (own_update with "H"). apply auth_update. rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:Hd; last by inversion H.
  rewrite insert_delete_insert fmap_insert. eapply singleton_local_update.
  { by rewrite lookup_fmap Hd /=. }
  destruct d as [[dl ds] dw]. inversion H; subst ds; simpl.
  repeat apply prod_local_update; try done. simpl.
  apply delete_option_local_update. apply _.
Qed.

Lemma helped_to_done γs i γ slots :
  state_of <$> slots !! i = Some (Help γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ ==∗
    own γs (● (of_slot_data <$> update_slot i to_done slots) : slotUR).
Proof.
  iIntros (H) "H1 H2". by iMod (helped_to_done_aux with "H1 H2") as "[H _]".
Qed.

Lemma val_wit_from_auth γs i l slots :
  val_of <$> slots !! i = Some l →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> slots) : slotUR) ∗
    slot_val_wit γs i l.
Proof.
  iIntros (H) "H". rewrite -own_op. iApply (own_update with "H").
  apply auth_update_dfrac_alloc; first apply _.
  assert (∃ d, slots !! i = Some d) as [d Hlookup].
  { destruct (slots !! i) as [d|]; inversion H. by exists d. }
  apply singleton_included_l. rewrite lookup_fmap. rewrite Hlookup /=.
  exists (of_slot_data d). split; first done.
  apply Some_included. right. destruct d as [[dl ds] dw]. simpl.
  repeat (apply prod_included; split; simpl);
    try by (apply option_included; left).
  apply option_included; right. exists (to_agree l), (to_agree dl).
  repeat (split; first done). left.
  rewrite Hlookup /= in H. by inversion H.
Qed.

(** * Prophecy abstractions *************************************************)

Fixpoint proph_data sz (deq : gset nat) (rs : list (val * val)) : list nat :=
  match rs with
  | (PairV _ #true , LitV (LitInt i)) :: rs =>
    if decide (0 ≤ i < sz)%Z then
      let i := Z.to_nat i in
      if decide (i ∈ deq) then
        []
      else
        i :: proph_data sz ({[i]} ∪ deq) rs
    else []
  | (PairV _ #false, LitV (LitInt i)) :: rs =>
    if decide (0 ≤ i < sz)%Z then
      proph_data sz deq rs
    else
      []
  | _                               => []
  end.

(* Wrapper for the Iris [proph] proposition, using our data abstraction. *)
Definition hwq_proph p sz deq pvs :=
  (∃ rs, proph p rs ∗ ⌜pvs = proph_data sz deq rs⌝)%I.

Lemma proph_data_deq sz deq rs : ∀ i, i ∈ deq → i ∉ proph_data sz deq rs.
Proof.
  revert deq. induction rs as [|[b k] rs IH]; intros deq i Hi.
  - apply not_elem_of_nil.
  - destruct b as [| |b1 b2| |]; simpl; try by apply not_elem_of_nil.
    destruct b2 as [lit| | | |]; simpl; try by apply not_elem_of_nil.
    destruct lit as [|b| | | |]; simpl; try by apply not_elem_of_nil.
    destruct b.
    + destruct k as [lit | | | |]; simpl; try by apply not_elem_of_nil.
      destruct lit as [n| | | | |]; simpl; try by apply not_elem_of_nil.
      destruct (decide (0 ≤ n < sz)%Z); last by apply not_elem_of_nil.
      destruct (decide (Z.to_nat n ∈ deq)); first by apply not_elem_of_nil.
      apply not_elem_of_cons. split; first by set_solver.
      apply IH. set_solver.
    + destruct k as [lit | | | |]; simpl; try by apply not_elem_of_nil.
      destruct lit as [n| | | | |]; simpl; try by apply not_elem_of_nil.
      destruct (decide (0 ≤ n < sz)%Z); last by apply not_elem_of_nil.
      apply IH. done.
Qed.

Lemma proph_data_sz sz deq rs : ∀ i, i ∈ proph_data sz deq rs → i < sz.
Proof.
  revert deq. induction rs as [|[b k] rs IH]; intros deq i Hi.
  - set_solver.
  - destruct b as [| |b1 b2| |]; simpl; try by set_solver.
    destruct b2 as [lit| | | |]; simpl; try by set_solver.
    destruct lit as [|b| | | |]; simpl; try by set_solver.
    destruct b.
    + destruct k as [lit | | | |]; simpl; try by set_solver.
      destruct lit as [n| | | | |]; simpl; try by set_solver.
      simpl in Hi.
      destruct (decide (0 ≤ n < sz)%Z) as [Hn|Hn]; last by set_solver.
      destruct (decide (Z.to_nat n ∈ deq)) as [H|H]; first by set_solver.
      apply elem_of_cons in Hi. destruct Hi as [->|Hi].
      * apply Nat2Z.inj_lt. destruct Hn as [Hn1 Hn2]. by rewrite Z2Nat.id.
      * by apply (IH _ _ Hi).
    + destruct k as [lit | | | |]; simpl; try by set_solver.
      destruct lit as [n| | | | |]; simpl; try by set_solver.
      simpl in Hi.
      destruct (decide (0 ≤ n < sz)%Z); last by set_solver.
      apply (IH _ _ Hi).
Qed.

Lemma proph_data_NoDup sz deq rs :
  NoDup (proph_data sz deq rs ++ elements deq).
Proof.
  revert deq. induction rs as [|[b k] rs IH]; intros deq.
  - apply NoDup_elements.
  - destruct b as [| |b1 b2| |]; simpl; try by apply NoDup_elements.
    destruct b2 as [lit| | | |]; simpl; try by apply NoDup_elements.
    destruct lit as [|b| | | |]; simpl; try by apply NoDup_elements.
    destruct b.
    + destruct k as [lit| | | |]; simpl; try by apply NoDup_elements.
      destruct lit as [n| | | | |]; simpl; try by apply NoDup_elements.
      destruct (decide (0 ≤ n < sz)%Z)
        as [Hn|Hn]; last by apply NoDup_elements.
      destruct (decide (Z.to_nat n ∈ deq))
        as [Hn_in_deq|Hn_not_in_deq]; first by apply NoDup_elements.
      specialize (IH ({[Z.to_nat n]} ∪ deq)) as H1.
      assert (Z.to_nat n ∉ proph_data sz ({[Z.to_nat n]} ∪ deq) rs) as H2.
      { apply proph_data_deq. by set_solver. }
      apply NoDup_app in H1 as (H1_1 & H1_2 & H1_3).
      apply NoDup_app. repeat split_and.
      * by apply NoDup_cons.
      * intros i Hi. apply elem_of_cons in Hi as [Hi|Hi]; first by set_solver.
        intros H_elements%elem_of_elements.
        eapply (proph_data_deq sz ({[Z.to_nat n]} ∪ deq) rs i); by set_solver.
      * by apply NoDup_elements.
    + destruct k as [lit| | | |]; simpl; try by apply NoDup_elements.
      destruct lit as [n| | | | |]; simpl; try by apply NoDup_elements.
      destruct (decide (0 ≤ n < sz)%Z); [ by apply IH | by apply NoDup_elements ].
Qed.

Definition block  : Type := nat * list nat.
Definition blocks : Type := list block.

(* A block is valid if it follows the structure described above. *)
Definition block_valid slots (b : block) :=
  slots !! b.1 = None ∧
  ∀ i, i ∈ b.2 → was_committed <$> (slots !! i) = Some false.

Fixpoint glue_blocks (b : block) (i : nat) (bs : blocks) : blocks :=
  match bs with
  | []               => [b]
  | (j, pends) :: bs => if decide (i = j) then (b.1, b.2 ++ i :: pends) :: bs
                        else b :: glue_blocks (j, pends) i bs
  end.

Fixpoint flatten_blocks bs : list nat :=
  match bs with
  | []               => []
  | (i, pends) :: bs => i :: pends ++ flatten_blocks bs
  end.

Lemma blocks_elem1 b blocks :
  b ∈ blocks → b.1 ∈ flatten_blocks blocks.
Proof.
  intros H. induction blocks as [|b' blocks IH]; first by inversion H.
  destruct (decide (b' = b)) as [->|Hb_not_b'].
  - destruct b as [b_u b_ps]. by apply elem_of_list_here.
  - destruct b' as [b'_u b'_bs]. simpl.
    apply elem_of_list_further. apply elem_of_app; right.
    apply IH. apply elem_of_cons in H as [H|H]; last done.
    by rewrite H in Hb_not_b'.
Qed.

Lemma blocks_elem2 b blocks :
  b ∈ blocks → ∀ i, i ∈ b.2 → i ∈ flatten_blocks blocks.
Proof.
  intros H. induction blocks as [|b' blocks IH]; first by inversion H.
  destruct (decide (b' = b)) as [->|Hb_not_b'].
  - destruct b as [b_u b_ps]. intros i Hi. simpl in *.
    apply elem_of_list_further. apply elem_of_app. by left.
  - destruct b' as [b'_u b'_bs]. simpl. intros i Hi.
    apply elem_of_list_further. apply elem_of_app; right.
    apply IH; last done. apply elem_of_cons in H as [H|H]; last done.
    by rewrite H in Hb_not_b'.
Qed.

Lemma glue_blocks_valid slots i b_unused b_pendings blocks l γ :
  slots !! i = None →
  b_unused ≠ i →
  NoDup (b_unused :: b_pendings ++ flatten_blocks blocks) →
  (∀ b : block, b ∈ (b_unused, b_pendings) :: blocks → block_valid slots b) →
  ∀ b, b ∈ glue_blocks (b_unused, b_pendings) i blocks → block_valid (<[i:=(l, Pend γ, false)]> slots) b.
Proof using Type*.
  intros Hi. revert b_unused b_pendings.
  induction blocks as [|[b_u b_ps] blocks IH];
    intros b_unused b_pendings Hb_unused_not_i HND Hblocks_valid [b_u' b_ps'] Hb.
  - apply Hblocks_valid in Hb as Hvalid.
    apply elem_of_list_singleton in Hb. simplify_eq.
    destruct Hvalid as (Hvalid1 & Hvalid2). split.
    + by rewrite lookup_insert_ne.
    + simpl in *. intros k Hk. specialize (Hvalid2 _ Hk) as Hvalid_k.
      destruct (decide (k = i)) as [->|Hk_not_i].
      * by rewrite lookup_insert.
      * by rewrite lookup_insert_ne.
  - simpl in Hb. destruct (decide (i = b_u)) as [->|Hi_not_b_u].
    + apply elem_of_cons in Hb as [Hb|Hb].
      * simplify_eq.
        assert ((b_unused, b_pendings) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2).
        assert ((b_u, b_ps) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid'%Hblocks_valid by set_solver.
        destruct Hvalid' as (Hvalid1' & Hvalid2').
        split; simpl.
        ** by rewrite lookup_insert_ne.
        ** intros k Hk. apply elem_of_app in Hk as [Hk|Hk].
           *** assert (k ≠ b_u) as HNEq2.
               { apply NoDup_cons in HND as (_ & HND).
                 apply NoDup_app in HND as (_ & HND & _). apply HND in Hk.
                 simpl in Hk. by apply not_elem_of_cons in Hk as (Hk & _). }
               rewrite lookup_insert_ne; last done. by apply Hvalid2.
           *** apply elem_of_cons in Hk as [->|Hk]; first by rewrite lookup_insert.
               assert (b_u ≠ k) as HNEq2.
               { apply NoDup_cons in HND as (_ & HND).
                 apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
                 apply NoDup_cons in HND as (HND & _).
                 apply not_elem_of_app in HND as (HND & _).
                 intros ->. apply HND, Hk. }
               rewrite lookup_insert_ne; last done. by apply Hvalid2'.
      * assert ((b_u', b_ps') ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2). rewrite /block_valid.
        assert (b_u ≠ b_u') as HNeq1.
        { apply NoDup_cons in HND as (_ & HND).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          apply NoDup_cons in HND as (HND & _). intros <-.
          apply not_elem_of_app in HND as (_ & HND). apply HND.
          by apply blocks_elem1 in Hb. }
        rewrite lookup_insert_ne; last done. split; first done.
        intros k Hk. simpl in Hk.
        assert (b_u ≠ k) as HNeq2.
        { apply NoDup_cons in HND as (_ & HND).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          apply NoDup_cons in HND as (HND & _). intros <-.
          apply not_elem_of_app in HND as (_ & HND). apply HND.
          by eapply blocks_elem2 in Hb. }
        rewrite lookup_insert_ne; last done. by apply Hvalid2.
    + apply elem_of_cons in Hb as [Hb|Hb].
      * simplify_eq.
        assert ((b_unused, b_pendings) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2). split.
        ** by rewrite lookup_insert_ne.
        ** intros k Hk. simpl in *.
           assert (k ≠ i) as HNEq.
           { intros ->. apply Hvalid2 in Hk. rewrite Hi in Hk. by inversion Hk. }
           rewrite lookup_insert_ne; last done. by apply Hvalid2.
      * eapply IH; last done; first done.
        { apply NoDup_cons in HND as (_ & HND).
          by apply NoDup_app in HND as (_ & _ & HND). }
        intros b' Hb'.
        assert (b' ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hb'_valid%Hblocks_valid by set_solver. done.
Qed.

(* Contradiction status: either there is a contradiction going on with
   the given indices, or there is no contradiction. In the latter case
   the prophecy has well-formed pending blocks as a suffix. *)
Inductive cont_status :=
  | WithCont : nat → nat → cont_status
  | NoCont   : blocks    → cont_status.

Local Instance cont_status_inhabited : Inhabited cont_status.
Proof. constructor. refine (NoCont []). Qed.

Lemma initial_block_valid b pvs :
  b ∈ map (λ i : nat, (i, [])) pvs → block_valid ∅ b.
Proof.
  intros H. induction pvs as [|i pvs IH].
  - by inversion H.
  - simpl in H. apply elem_of_cons in H as [->|H].
    + split; first by apply lookup_empty. intros k Hk. by inversion Hk.
    + apply IH, H.
Qed.

Lemma flatten_blocks_initial pvs :
  pvs = flatten_blocks (map (λ i : nat, (i, [])) pvs).
Proof.
  induction pvs as [|i pvs IH]; first done.
  simpl. f_equal. by apply IH.
Qed.

Lemma flatten_blocks_glue b bs i :
  flatten_blocks (b :: bs) = flatten_blocks (glue_blocks b i bs).
Proof.
  revert b.
  induction bs as [|[b_u' b_ps'] bs IH]; intros [b_u b_ps]; first done.
  simpl. destruct (decide (i = b_u')) as [->|HNEq]; simpl.
  - by rewrite -app_assoc.
  - by rewrite -IH.
Qed.

Lemma flatten_blocks_mem1 blocks :
  ∀b, b ∈ blocks → b.1 ∈ flatten_blocks blocks.
Proof.
  intros b Hb. induction blocks as [|[i ps] bs IH]; first by inversion Hb.
  apply elem_of_cons in Hb as [->|Hb]; first by apply elem_of_list_here.
  simpl. apply elem_of_list_further. apply elem_of_app. right. by apply IH.
Qed.

Lemma flatten_blocks_mem2 blocks :
  ∀b, b ∈ blocks → ∀i, i ∈ b.2 → i ∈ flatten_blocks blocks.
Proof.
  intros b Hb. induction blocks as [|[i ps] bs IH]; first by inversion Hb.
  intros k Hk. apply elem_of_cons in Hb as [->|Hb]; simpl.
  - apply elem_of_list_further. apply elem_of_app. by left.
  - apply elem_of_list_further. apply elem_of_app. right. by apply IH.
Qed.

(** * Some definitions and lemmas about array content manipulation **********)

Definition array_get slots (deqs : gset nat) i :=
  match slots !! i with
  | None   => NONEV
  | Some d => if decide (i ∈ deqs) then NONEV
              else physical_value d
  end.

Fixpoint array_content n slots deqs :=
  match n with
  | 0 => []
  | S n   => array_content n slots deqs ++ [array_get slots deqs n]
  end.

Lemma length_array_content sz slots deqs :
  length (array_content sz slots deqs) = sz.
Proof.
  induction sz as [|sz IH]; first done.
  by rewrite /= app_length Nat.add_comm /= IH.
Qed.

Lemma array_content_lookup sz slots deqs i :
  i < sz →
  array_content sz slots deqs !! i = Some (array_get slots deqs i).
Proof.
  intros H. induction sz as [|sz IH]; first lia.
  destruct (decide (i = sz)) as [->|Hi_not_sz]; simpl.
  - rewrite lookup_app_r length_array_content; last done.
    by rewrite Nat.sub_diag /=.
  - rewrite lookup_app_l; first (apply IH; by lia).
    rewrite length_array_content. lia.
Qed.

Lemma array_content_empty sz :
  array_content sz ∅ ∅ = replicate sz NONEV.
Proof.
  induction sz as [|sz IH]; first done.
  rewrite replicate_S_end /= IH. done.
Qed.

Lemma array_content_NONEV sz i d slots deqs :
  physical_value d = NONEV → slots !! i = None → i ∉ deqs →
  array_content sz (<[i:=d]> slots) deqs = array_content sz slots deqs.
Proof.
  intros H1 H2 H3. induction sz as [|sz IH]; first done.
  rewrite /= /array_get. destruct (decide (i = sz)) as [->|Hi_not_sz].
  - rewrite lookup_insert H2 decide_False; last done. by rewrite IH H1.
  - rewrite lookup_insert_ne; last done. by rewrite IH.
Qed.

Lemma array_content_is_Some sz i slots deqs :
  i < sz →
  is_Some (array_content sz slots deqs !! i).
Proof.
  intros H. apply lookup_lt_is_Some. by rewrite length_array_content.
Qed.

Lemma array_content_ext sz slots1 slots2 deqs :
  (∀ i, i < sz → array_get slots1 deqs i = array_get slots2 deqs i) →
  array_content sz slots1 deqs = array_content sz slots2 deqs.
Proof.
  induction sz as [|sz IH]; intros H; first done.
  simpl. rewrite H; last by lia. f_equal. apply IH.
  intros i Hi. apply H. by lia.
Qed.

Lemma array_content_more_deqs sz slots deqs i :
  sz ≤ i →
  array_content sz slots ({[i]} ∪ deqs) = array_content sz slots deqs.
Proof.
  intros H. induction sz as [|sz IH]; first done.
  rewrite /= IH; last by lia. f_equal.
  rewrite /array_get. destruct (slots !! sz) as [d|]; last done.
  destruct (decide (sz ∈ deqs)) as [Helem|Hnot_elem].
  - rewrite decide_True; [ done | by set_solver ].
  - rewrite decide_False; [ done | .. ].
    apply not_elem_of_union. split; last done.
    apply not_elem_of_singleton. by lia.
Qed.

Lemma array_content_update_slot_ge sz slots deqs f i :
  sz ≤ i →
  array_content sz slots deqs = array_content sz (update_slot i f slots) deqs.
Proof.
  intros H. induction sz as [|sz IH]; first done.
  rewrite /= IH; last by lia. f_equal.
  rewrite /array_get /update_slot.
  destruct (slots !! i) as [d|]; last done.
  rewrite insert_delete_insert. rewrite lookup_insert_ne; [ done | by lia ].
Qed.

Lemma array_content_dequeue sz i slots deqs :
  i < sz →
  i ∉ deqs →
  array_content sz slots ({[i]} ∪ deqs) = <[i:=NONEV]> (array_content sz slots deqs).
Proof using Type*.
  revert i. induction sz as [|sz IH]; intros i H1 H2; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0 NONEV).
    rewrite /= /array_get. destruct (slots !! i) as [d|].
    + rewrite decide_True; last by set_solver. f_equal.
      rewrite array_content_more_deqs; [ done | by lia ].
    + f_equal. rewrite array_content_more_deqs; [ done | by lia ].
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done ]. f_equal.
    rewrite /array_get. destruct (slots !! sz) as [d|]; last done.
    destruct (decide (sz ∈ deqs)) as [H|H].
    * rewrite decide_True; [ done | by set_solver ].
    * rewrite decide_False; [ done | by set_solver ].
Qed.

Lemma array_content_set_written sz i (l : loc) slots deqs :
  i < sz →
  val_of <$> slots !! i = Some l →
  ¬ i ∈ deqs →
  <[i:=InjRV #l]> (array_content sz slots deqs) = array_content sz (update_slot i set_written slots) deqs.
Proof using Type*.
  revert i. induction sz as [|sz IH]; intros i H1 H2 H3; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0).
    erewrite array_content_update_slot_ge; [ f_equal | by lia ].
    rewrite /= /array_get /update_slot. destruct (slots !! i) as [d|].
    + rewrite lookup_insert decide_False; last done.
      destruct d as [[ld sd] wd]. inversion H2; subst ld. done.
    + inversion H2.
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done | done ]. f_equal.
    rewrite /array_get /update_slot. destruct (slots !! i) as [d|]; last done.
    by rewrite insert_delete_insert lookup_insert_ne.
Qed.

(* FIXME similar to previous lemma. Share stuff? *)
Lemma array_content_set_written_and_done sz i (l : loc) slots deqs :
  i < sz →
  val_of <$> slots !! i = Some l →
  ¬ i ∈ deqs →
  <[i:=InjRV #l]> (array_content sz slots deqs) = array_content sz (update_slot i set_written_and_done slots) deqs.
Proof.
  revert i. induction sz as [|sz IH]; intros i H1 H2 H3; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0).
    erewrite array_content_update_slot_ge; [ f_equal | by lia ].
    rewrite /= /array_get /update_slot. destruct (slots !! i) as [d|].
    + rewrite lookup_insert decide_False; last done.
      destruct d as [[ld sd] wd]. inversion H2; subst ld. done.
    + inversion H2.
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done | done ]. f_equal.
    rewrite /array_get /update_slot. destruct (slots !! i) as [d|]; last done.
    by rewrite insert_delete_insert lookup_insert_ne.
Qed.

Lemma update_slot_lookup i f slots :
  update_slot i f slots !! i = f <$> slots !! i.
Proof.
  rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq; last done.
  by rewrite lookup_insert.
Qed.

Lemma update_slot_lookup_ne i k f slots :
  i ≠ k →
  update_slot i f slots !! k = slots !! k.
Proof.
  intros H. rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq; last done.
  rewrite lookup_insert_ne; last done.
  by rewrite lookup_delete_ne.
Qed.

Lemma update_slot_update_slot i f g slots :
  update_slot i f (update_slot i g slots) = update_slot i (f ∘ g) slots.
Proof.
  rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq.
  - rewrite lookup_insert. repeat rewrite insert_delete_insert.
    rewrite insert_insert. done.
  - rewrite HEq. done.
Qed.

Definition get_value slots (deqs : gset nat) i : loc :=
  match slots !! i with
  | None   => inhabitant
  | Some d => val_of d
  end.

Definition map_get_value_not_in_pref i d pref slots deqs :
  was_written d = false →
  i ∉ pref →
  map (get_value (<[i:=d]> slots) deqs) pref = map (get_value slots deqs) pref.
Proof.
  intros Hd. induction pref as [|k pref IH]; intros Hi; first done.
  rewrite /= IH; last by set_solver. f_equal. rewrite /get_value.
  rewrite lookup_insert_ne; first done. set_solver.
Qed.

(** * Definition of the main ************************************************)

(** Atomic update for the insertion of [l], with post-condition [Q]. *)
Definition enqueue_AU γe l Q :=
  (AU <{ ∃∃ ls : list loc, hwq_cont γe ls }> @ ⊤ ∖ ↑N, ∅
      <{ hwq_cont γe (ls ++ [l]), COMM Q }>)%I.

(*
When a contradiction is going on, we have [cont = WithCont i1 i2] where:
 - [i1] is the index reserved by the enqueue operation the initiated the
   contradiction,
 - [i2] is the first index in the prophecy that was not yet reserved for
   an enqueue operation (when the contradiction was initiated).
*)

Definition per_slot_own γe γs i d :=
  (slot_val_wit γs i (val_of d) ∗
  (if was_written d then slot_written_wit γs i else True) ∗
  match state_of d with
  | Pend γ => slot_pending_tok γs i ∗
              ∃ Q, saved_prop_own γ DfracDiscarded Q ∗ enqueue_AU γe (val_of d) Q
  | Help γ => slot_committed_wit γs i ∗ ∃ Q, saved_prop_own γ DfracDiscarded Q ∗ ▷ Q
  | Done   => slot_committed_wit γs i ∗ slot_token γs i
  end)%I.

Definition inv_hwq sz γb γi γe γc γs ℓ_ar ℓ_back p : iProp :=
  (∃ (back  : nat)                (** Physical value of [q.back]. *)
     (pvs   : list nat)           (** Full contents of the prophecy. *)
     (pref  : list nat)           (** Commit prefix of the prophecy *)
     (rest  : list loc)           (** Logical queue after commit prefix. *)
     (cont  : cont_status)        (** Contradiction or prophecy suffix. *)
     (slots : gmap nat slot_data) (** Per-slot data for used indices. *)
     (deqs  : gset nat),          (** Dequeued indices. *)
  (** Physical data. *)
  ℓ_back ↦ #back ∗ ℓ_ar ↦∗ (array_content sz slots deqs) ∗
  (** Logical contents of the queue and prophecy contents. *)
  back_value γb back ∗
  i2_lower_bound γi (match cont with WithCont _ i2 => i2 | NoCont _ => back `min` sz end) ∗
  own γe (● (Excl' (map (get_value slots deqs) pref ++ rest))) ∗
  own γs (● (of_slot_data <$> slots : gmap nat per_slot)) ∗
  hwq_proph p sz deqs pvs ∗
  (** Per-slot ownership. *)
  ([∗ map] i ↦ d ∈ slots, per_slot_own γe γs i d) ∗
  (** Contradiction status. *)
  match cont with NoCont _ => no_contra γc | WithCont i1 i2 => contra γc i1 i2 end ∗
  (** Tying the logical and physical data and some other pure stuff. *)
  ⌜(∀ i, (i < back `min` sz) ↔ is_Some (slots !! i)) ∧
   (∀ i, (was_committed <$> slots !! i = Some false → was_written <$> slots !! i = Some false) ∧
         (was_written <$> slots !! i = Some false → i ∉ deqs)) ∧
   (∀ i, i ∈ pref → was_committed <$> slots !! i = Some true ∧ i ∉ deqs ∧
                    match cont with WithCont i1 _ => i ≠ i1 | _ => True end) ∧
   (∀ i, i ∈ deqs → was_written <$> slots !! i = Some true ∧
                    was_committed <$> slots !! i = Some true ∧
                    array_get slots deqs i = NONEV) ∧
   (NoDup (pvs ++ elements deqs) ∧ ∀ i, i ∈ pvs → i < sz) ∧
   match cont with
   | NoCont bs      =>
     (∀ b, b ∈ bs → block_valid slots b) ∧
     (bs ≠ [] → rest = []) ∧
     pvs = pref ++ flatten_blocks bs
   | WithCont i1 i2 =>
     (i1 < i2 < sz ∧ i1 < back) ∧
     was_committed <$> slots !! i1 = Some true ∧
     was_written <$> slots !! i1 = Some true ∧ ¬ i1 ∈ deqs ∧
     array_get slots deqs i1 ≠ NONEV ∧
     pref ++ [i2] `prefix_of` pvs
  end⌝)%I.

Definition is_hwq sz γe v : iProp :=
  (∃ γb γi γc γs ℓ_ar ℓ_back p,
    ⌜v = (#sz, #ℓ_ar, #ℓ_back, #p)%V⌝ ∗
    inv N (inv_hwq sz γb γi γe γc γs ℓ_ar ℓ_back p))%I.

(** * Some useful instances *************************************************)

Local Instance blocks_match_persistent (bs : blocks) γc i1 :
  Persistent (match bs with
              | []           => True
              | (i2, _) :: _ => contra γc i1 i2
              end)%I.
Proof. destruct bs as [|[i2 _] _]; apply _. Qed.

Local Instance cont_match_persistent cont γc :
  Persistent (match cont with
              | NoCont _       => True
              | WithCont i1 i2 => contra γc i1 i2
              end)%I.
Proof. destruct cont as [i1 i2|_]; apply _. Qed.

Local Instance contra_timeless cont γc :
  Timeless (match cont with
            | NoCont _       => no_contra γc
            | WithCont i1 i2 => contra γc i1 i2
            end).
Proof. destruct cont as [i1 i2|_]; apply _. Qed.

(** * Some important lemmas for the specification of [enqueue] **************)

Definition get_values (slots : gmap nat slot_data) (p : list nat) :=
  fold_right (λ i acc, match val_of <$> slots !! i with
                       | None   => acc
                       | Some l => l :: acc end) [] p.

Definition get_values_not_in n ps d s :
  n ∉ ps → get_values (<[n:=d]> s) ps = get_values s ps.
Proof.
  intros H. induction ps as [|p ps IH]; first done. simpl.
  assert (n ≠ p) as Hn_not_p by set_solver.
  rewrite lookup_insert_ne; last done.
  rewrite IH; first done. set_solver.
Qed.

Definition helped (p : list nat) (i : nat) d :=
  match state_of d with
  | Pend γ => if decide (i ∈ p) then
                Some (val_of d, Help γ, was_written d)
              else
                Some d
  | _      => Some d
  end.

Lemma is_Some_helped (p : list nat) i d : is_Some (helped p i d).
Proof.
  rewrite /helped. destruct (state_of d); try by eexists.
  destruct (decide (i ∈ p)); by eexists.
Qed.

Lemma map_imap_helped_nil slots : map_imap (helped []) slots = slots.
Proof.
  apply map_eq. intros i. rewrite map_lookup_imap.
  destruct (slots !! i) as [d|] eqn:HEq.
  - rewrite /helped /= HEq. by destruct (state_of d).
  - by rewrite /= HEq.
Qed.

Lemma annoying_lemma_1 slots deqs pref i l b_pendings :
  (∀ k, k ∈ pref → was_committed <$> slots !! k = Some true ∧ k ∉ deqs) →
  NoDup (pref ++ i :: b_pendings) →
  map (get_value (map_imap (helped b_pendings) (<[i:=(l, Done, false)]> slots)) deqs) pref =
  map (get_value slots deqs) pref.
Proof.
  intros Hpref HND.
  induction pref as [|pref_hd pref IH]; first done.
  assert (NoDup (pref ++ i :: b_pendings)) as HND_IH.
  { simpl in HND. apply NoDup_cons in HND as [_ HND]. done. }
  assert (∀ k, k ∈ pref → was_committed <$> slots !! k = Some true ∧
                          k ∉ deqs) as Hpref_IH.
  { intros k Hk. by apply Hpref, elem_of_list_further, Hk. }
  rewrite /= IH; try done. clear IH HND_IH Hpref_IH. f_equal.
  assert (i ≠ pref_hd) as Hi_not_pref_hd.
  { simpl in HND. apply NoDup_cons in HND as (HND & _).
    apply not_elem_of_app in HND as (_ & HND).
    by apply not_elem_of_cons in HND as (HND & _). }
  rewrite /get_value map_lookup_imap lookup_insert_ne; last done.
  destruct (slots !! pref_hd) as [[[lp sp] wp]|]; last done.
  destruct sp; try done. rewrite /= /helped /=.
  rewrite decide_False; first done.
  simpl in HND. apply NoDup_cons in HND as (HND & _).
  apply not_elem_of_app in HND as (_ & HND).
  by apply not_elem_of_cons in HND as (_ & HND).
Qed.

Lemma annoying_lemma_2 slots deqs pref i l b_pendings :
  block_valid slots (i, b_pendings) →
  NoDup (pref ++ i :: b_pendings) →
  map (get_value (map_imap (helped b_pendings) (<[i:=(l, Done, false)]> slots)) deqs) b_pendings =
  get_values (<[i:=(l, Done, false)]> slots) b_pendings.
Proof.
  intros (Hvalid_1 & Hvalid_2) HND.
  induction b_pendings as [|p ps IH]; first done. simpl in *.
  assert (i ≠ p) as Hi_not_p.
  { intros ->. apply NoDup_app in HND as (_ & _ & HND).
    apply NoDup_cons in HND as (HND & _). by set_solver +HND. }
  rewrite lookup_insert_ne; last done.
  assert (p ∈ p :: ps) as Hcomm%Hvalid_2 by set_solver.
  destruct (slots !! p)
    as [[[lp sp] wp]|] eqn:Hslots_p; [ f_equal | by inversion Hcomm ].
  - rewrite /= map_imap_insert /helped /= /get_value.
    rewrite lookup_insert_ne; last done. rewrite map_lookup_imap Hslots_p /=.
    destruct sp; try done. rewrite decide_True; [ done | by set_solver ].
  - rewrite -IH; first last; try done.
    { apply NoDup_app in HND as (HND1 & HND2 & HND3).
      apply NoDup_app. split; first done. split.
      - intros e He. apply HND2 in He. apply not_elem_of_cons.
        split; by set_solver +He.
      - apply NoDup_cons in HND3 as (HND3_1 & HND3_2).
        apply NoDup_cons. split; first by set_solver +HND3_1.
        apply NoDup_cons in HND3_2 as (HND3_2_1 & HND3_2_2). done. }
    { intros k Hk. by apply Hvalid_2, elem_of_list_further, Hk. }
    apply map_ext_in. intros k Hk.
    rewrite /get_value map_lookup_imap map_lookup_imap.
    assert (i ≠ k) as Hi_not_k.
    { intros ->. apply NoDup_app in HND as (_ & _ & HND).
      apply NoDup_cons in HND as (HND & _).
      apply not_elem_of_cons in HND as (_ & HND).
      by apply HND, elem_of_list_In, Hk. }
    rewrite lookup_insert_ne; last done.
    assert (k ∈ p :: ps) as Hk_p_ps
      by by apply elem_of_list_further, elem_of_list_In.
    specialize (Hvalid_2 _ Hk_p_ps) as Hcomm_k.
    destruct (slots !! k) as [[[lk sk] wk]|]; last by inversion Hcomm_k.
    destruct sk; try done. rewrite /= /helped /=.
    rewrite decide_True; last done.
    rewrite decide_True; [ done | by apply elem_of_list_In ].
Qed.

Lemma big_lemma γe γs (ls : list loc) slots (p : list nat) :
  NoDup p →
  (∀ i, i ∈ p → was_committed <$> slots !! i = Some false) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
   ([∗ map] i ↦ d ∈ slots, per_slot_own γe γs i d) -∗
   own γe (● (Excl' ls)) ={⊤ ∖ ↑N}=∗
    own γs (● (of_slot_data <$> map_imap (helped p) slots) : slotUR) ∗
    ([∗ map] i ↦ d ∈ map_imap (helped p) slots, per_slot_own γe γs i d) ∗
    own γe (● (Excl' (ls ++ get_values slots p))).
Proof.
  revert p. iIntros (p).
  iInduction p as [|n ps] "IH" forall (slots ls); iIntros (HNoDup H) "Hs● Hbig He●".
  - iModIntro. rewrite /= app_nil_r map_imap_helped_nil. iFrame.
  - assert (∀ i : nat, i ∈ ps → was_committed <$> slots !! i = Some false) as H1.
    { intros i Hi. apply H. apply elem_of_list_further, Hi. }
    assert (was_committed <$> slots !! n = Some false) as H2.
    { apply H. apply elem_of_list_here. }
    assert (∃ ln γn wn, slots !! n = Some (ln, Pend γn, wn)) as Hn.
    { destruct (slots !! n) as [[[ln sn] wn]|]; last by inversion H2.
      (destruct sn as [γn|γn|]; last by inversion H2); by exists ln, γn, wn. }
    apply NoDup_cons in HNoDup. destruct HNoDup as [Hn_not_in_ps HNoDup].
    destruct Hn as [l [γ [w Hn]]].
    assert (slots = <[n:=(l, Pend γ, w)]> (delete n slots)) as Hs.
    { by rewrite insert_delete_insert insert_id. }
    rewrite [in ([∗ map] _ ↦ _ ∈ slots, _)%I]Hs.
    iDestruct (big_sepM_insert with "Hbig")
      as "[Hbig_n Hbig]"; first by apply lookup_delete.
    iDestruct "Hbig_n" as "[Hval_wit_n [Hwritten_n [Hpending_tok_n H]]]".
    iDestruct "H" as (Q) "[Hsaved AU]".
    iMod "AU" as (elts_AU) "[He◯ [_ Hclose]]".
    iDestruct (sync_elts with "He● He◯") as %<-.
    iMod (update_elts _ _ _ (ls ++ [l]) with "He● He◯") as "[He● He◯]".
    iMod ("Hclose" with "[$He◯]") as "HPost".
    iMod (use_pending_tok with "Hs● Hpending_tok_n")
      as "[Hs● Hcommitted_wit_n]"; first by rewrite Hn.
    iCombine "Hsaved HPost" as "Hn".
    iDestruct (big_sepM_insert _ (delete n slots) n (l, Help γ, w)
      with "[Hn Hval_wit_n Hwritten_n Hcommitted_wit_n Hbig]")
      as "Hbig"; first by apply lookup_delete.
    { iClear "IH". iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
      iExists Q. iDestruct "Hn" as "[$ HPost]". iNext. done. }
    rewrite insert_delete_insert /update_slot Hn insert_delete_insert.
    assert (∀ i : nat, i ∈ ps → was_committed <$> <[n:=(l, Help γ, w)]> slots !! i = Some false) as HHH.
    { intros i Hi. rewrite lookup_insert_ne; [ by apply H1 | by set_solver ]. }
    iMod ("IH" $! (<[n:=(l, Help γ, w)]> slots) (ls ++ [l]) HNoDup HHH
            with "Hs● Hbig He●") as "[Hs● [Hbig He●]]"; iClear "IH".
    assert (map_imap (helped ps) (<[n:=(l, Help γ, w)]> slots)
            = map_imap (helped (n :: ps)) slots) as ->.
    { apply map_eq. intros i. destruct (decide (i = n)) as [->|Hi_not_n].
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert Hn /=.
        rewrite /helped /=. rewrite decide_True; first done. set_solver.
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert_ne; last done.
        destruct (slots !! i) as [[[li si] wi]|]; last done. simpl.
        rewrite /helped /=. destruct si; try done.
        destruct (decide (i ∈ n :: ps)).
        + rewrite decide_True; first done. set_solver.
        + rewrite decide_False; first done. set_solver. }
    iModIntro. iFrame.
    by rewrite /= Hn -app_assoc /= get_values_not_in.
Qed.

Lemma array_contents_cases γs slots deqs i li :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_val_wit γs i li -∗
    ⌜array_get slots deqs i = SOMEV #li ∨ array_get slots deqs i = NONEV⌝.
Proof.
  iIntros "Hs● Hval_wit_i".
  iDestruct (use_val_wit with "Hs● Hval_wit_i") as %Hslots_i.
  destruct (slots !! i) as [d|] eqn:HEq; last by inversion Hslots_i.
  destruct d as [[li' si] wi]. inversion Hslots_i as [H]; subst li'.
  rewrite /array_get HEq. simpl. iPureIntro.
  destruct (decide (i ∈ deqs)); first by right.
  destruct wi; by [ left | right ].
Qed.

(** * Specification of the queue operations *********************************)

Lemma new_queue_spec sz :
  0 < sz →
  {{{ True }}}
    new_queue #sz
  {{{ v γ, RET v; is_hwq sz γ v ∗ hwq_cont γ [] }}}.
Proof.
  iIntros (Hsz Φ) "_ HΦ". wp_lam.
  (** Allocate [q.ar], [q.back] and [q.p]. *)
  wp_apply wp_allocN; [ lia | done | ]. iIntros (ℓa) "[Hℓa _]".
  wp_alloc ℓb as "Hℓb". wp_pures.
  wp_apply wp_new_proph; [ done | ]. iIntros (rs p) "Hp".
  wp_pures.
  (* Allocate the remaining ghost state. *)
  iMod new_back as (γb) "Hb●".
  iMod new_back as (γi) "Hi●". (* FIXME not about back. *)
  iMod (new_elts []) as (γe) "[He● He◯]".
  iMod new_no_contra as (γc) "HC".
  iMod new_slots as (γs) "Hs●".
  (* Allocate the invariant. *)
  iMod (inv_alloc N _ (inv_hwq sz γb γi γe γc γs ℓa ℓb p)
    with "[Hℓa Hℓb Hp Hb● Hi● He● HC Hs●]") as "#InvN".
  { pose (pvs := proph_data sz ∅ rs).
    pose (cont := NoCont (map (λ i, (i, [])) pvs)).
    iNext. iExists 0, pvs, [], [], cont, ∅, ∅.
    rewrite array_content_empty Nat2Z.id fmap_empty /=.
    iFrame.
    repeat (iSplit; first done). iPureIntro.
    repeat split_and; try done.
    - intros i. split; intros Hi; [ by lia | by inversion Hi].
    - intros e He. set_solver.
    - apply proph_data_NoDup.
    - intros i. apply proph_data_sz.
    - intros b. apply initial_block_valid.
    - simpl. apply flatten_blocks_initial. }
  (* Wrap things up. *)
  iModIntro. iApply "HΦ". iFrame.
  iExists γb, γi, γc, γs, ℓa, ℓb, p. by iSplit.
Qed.

Lemma enqueue_spec sz γe (q : val) (l : loc) :
  is_hwq sz γe q -∗
  <<{ ∀∀ (ls : list loc), hwq_cont γe ls }>>
    enqueue q #l @ ↑N
  <<{ hwq_cont γe (ls ++ [l]) | RET #() }>>.
Proof.
  iIntros "Hq" (Φ) "AU".
  iDestruct "Hq" as (γb γi γc γs ℓ_ar ℓ_back p ->) "#Inv".
  rewrite /enqueue. wp_pures. wp_bind (FAA _ _)%E.
  (* Open the invariant to perform the increment. *)
  iInv "Inv" as (back pvs pref rest cont slots deqs) "HInv".
  iDestruct "HInv" as "[Hℓ_back [Hℓ_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]".
  iDestruct "HInv" as "[Hproph [Hbig [Hcont >Hpures]]]".
  iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
  destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
  wp_faa. assert (back + 1 = S back)%Z as -> by lia.
  iMod (back_incr with "Hb●") as "Hb●".
  iAssert (i2_lower_bound γi match cont with
                             | WithCont _ i2 => i2
                             | NoCont _ => back `min` sz
                             end -∗ |==>
            i2_lower_bound γi match cont with
                              | WithCont _ i2 => i2
                              | NoCont _      => (S back) `min` sz
                              end)%I as "Hup".
  { destruct cont as [i1 i2|bs]; iIntros "Hi●"; first done.
    iMod (i2_lower_bound_update with "Hi●") as "$"; [ lia | done ]. }
  iMod ("Hup" with "Hi●") as "Hi● {Hup}".
  (* We first handle the case where there is no more space in the queue. *)
  destruct (decide (back < sz)%Z) as [Hback_sz|Hback_sz]; last first.
  { iModIntro. iClear "AU". iSplitL.
    - iNext. iExists (S back), pvs, pref, rest, cont, slots, deqs.
      assert (S back `min` sz = back `min` sz) as -> by lia.
      iFrame. iPureIntro. repeat split_and; try done.
      destruct cont as [i1 i2|bs]; last done.
      destruct Hcont as ((H1 & H2) & H3 & H4).
      by repeat (split; first lia).
    - wp_pures. rewrite (bool_decide_false _ Hback_sz). wp_smart_apply wp_diverge. }
  (* We now have a reserved slot [i], which is still free. *)
  pose (i := back). pose (elts := map (get_value slots deqs) pref ++ rest).
  assert (slots !! back = None) as Hi_free.
  { destruct (Hslots i) as [H1 H2]. rewrite min_l in H1; last by lia.
    assert (¬ is_Some (slots !! back)). { intro H. apply H2 in H. lia. }
    apply eq_None_not_Some. eauto. }
  (* Useful fact: our index was not yet dequeued. *)
  assert (i ∉ deqs) as Hi_not_in_deq.
  { intros H. apply Hdeqs in H as (H & _). rewrite Hi_free in H. inversion H. }
  (* We then handle the case where there is a contradiction going on. *)
  destruct cont as [i1 i2|bs].
  { (* We access the atomic update and commit the element. *)
    iMod "AU" as (elts_AU) "[He◯ [_ Hclose]]".
    iDestruct (sync_elts with "He● He◯") as %<-.
    iMod (update_elts _ _ _ (elts ++ [l]) with "He● He◯") as "[He● He◯]".
    iMod ("Hclose" with "[$He◯]") as "HΦ".
    (* We allocate the new slot. *)
    iMod (alloc_done_slot γs slots i l Hi_free with "Hs●")
      as "[Hs [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
    (* We also remember that we had contradiciton states. *)
    iDestruct "Hcont" as "#cont_wit".
    (* And we can close the invariant. *)
    iModIntro. iSplitR "HΦ Hwriting_tok_i".
    { iNext. iExists (S back), pvs, pref, (rest ++ [l]), (WithCont i1 i2).
      iExists (<[i := (l, Done, false)]> slots), deqs.
      rewrite fmap_insert /= array_content_NONEV; try done. iFrame.
      iFrame. iSplitL "He●".
      { rewrite /elts app_assoc map_get_value_not_in_pref; try done.
        intros Hi%Hpref. rewrite Hi_free in Hi. destruct Hi; done. }
      iSplitL "Hbig Htok_i".
      { iApply big_sepM_insert.
        + apply eq_None_not_Some. intros H. apply Hslots in H. lia.
        + iFrame "Hbig". repeat (iSplit; first done). done. }
      iFrame "cont_wit".
      destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
      iPureIntro. repeat split_and; try done; try by lia.
      - intros k. destruct sz as [|sz]; first by lia.
        split; intros Hk.
        + destruct (decide (k = i)) as [->|k_not_i].
          * rewrite lookup_insert. by eexists.
          * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
        + destruct (decide (k = i)) as [->|k_not_i].
          * destruct sz; by lia.
          * rewrite lookup_insert_ne in Hk; last done.
            apply Hslots in Hk.  by lia.
      - intros k. destruct (decide (k = i)) as [->|k_not_i].
        + by rewrite lookup_insert.
        + rewrite lookup_insert_ne; last done. apply Hstate.
      - intros k Hk. destruct (decide (k = i)) as [->|HNeq].
        + split; first by rewrite lookup_insert. split; first done.
          intros ->. apply Hpref in Hk as (_ & _ & H). done.
        + rewrite lookup_insert_ne; last done. apply Hpref, Hk.
      - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
        + by rewrite lookup_insert.
        + rewrite /array_get. rewrite lookup_insert_ne; last done.
          apply Hdeqs in Hk as (H1 & H2 & H3). repeat (split; first done).
          rewrite /array_get in H3.
          destruct (slots !! k) as [[[dl ds] dw]|]; last done. done.
      - destruct (decide (i1 = i)) as [->|Hi1_not_i].
        + by rewrite lookup_insert.
        + by rewrite lookup_insert_ne.
      - rewrite /array_get lookup_insert_ne; first done. lia.
      - rewrite /array_get lookup_insert_ne; last by lia.
        destruct (slots !! i1) as [[[li1 si1] wi2]|]; last by inversion HC4.
        rewrite decide_False; last done. inversion HC5; subst wi2. done. }
    (* Let's clean up the context a bit. *)
    clear Hslots Hstate Hpref Hdeqs Hcont Hi_not_in_deq Hi_free Hpvs_ND Hpvs_sz.
    clear elts pvs pref rest slots deqs. subst i. rename back into i.
    (* We can now move to the store. *)
    wp_pures. rewrite (bool_decide_true _ Hback_sz).
    wp_pures. wp_bind (_ <- _)%E.
    (* We open the invariant again for the store. *)
    iInv "Inv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[Hℓ_back [Hℓ_ar [Hb● [Hi● [He● [>Hs● HInv]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [>Hcont >Hpures]]]".
    iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
    destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
    (* Using witnesses, we show that our value and state have not changed. *)
    iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
    iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
    iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
    (* We also show that the same contradiction ist still going on. *)
    destruct cont as [i1' i2'|bs]; last first.
    { by iDestruct (contra_not_no_contra with "Hcont cont_wit") as %Absurd. }
    iDestruct (contra_agree with "cont_wit Hcont") as %[-> ->].
    destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
    (* Our slot is mapped. *)
    assert (is_Some (slots !! i)) as Hslots_i.
    { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
    (* Our index is in the array. *)
    assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
    (* An we perform the store. *)
    wp_apply (wp_store_offset _ _ ℓ_ar i (array_content sz slots deqs) with "Hℓ_ar").
    { apply array_content_is_Some. by lia. }
    iIntros "Hℓ_ar".
    (* We perform some updates. *)
    iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
    iModIntro. iSplitR "HΦ"; last by wp_pures. iNext.
    (* It remains to re-establish the invariant. *)
    pose (new_slots := update_slot i set_written slots).
    iExists back, pvs, pref, rest, (WithCont i1 i2), new_slots, deqs.
    subst new_slots. iFrame. iSplitL "Hℓ_ar".
    { rewrite array_content_set_written;
        [ by iFrame | by lia | done | by apply Hstate ]. }
    iSplitL "He●".
    { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
      destruct (decide (k = i)) as [->|Hk_not_i].
      - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
        destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
        inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
      - rewrite update_slot_lookup_ne; last done. done. }
    iSplitL "Hbig".
    { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
      iApply big_sepM_insert; first by rewrite lookup_delete.
      assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
      { rewrite insert_delete_insert. by rewrite insert_id. }
      rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I] HEq_slots.
      iDestruct (big_sepM_insert with "Hbig")
        as "[[H1 [H2 H3]] $]"; first by rewrite lookup_delete.
      rewrite /per_slot_own val_of_set_written state_of_set_written.
      iFrame. by rewrite was_written_set_written. }
    iPureIntro.
    destruct Hslots_i as [[[li si] wi] Hslots_i].
    repeat split_and; try done.
    - intros k. destruct (decide (k = i)) as [->|k_not_i].
      + rewrite update_slot_lookup. split; intros H; last done.
        rewrite Hslots_i. by eexists.
      + rewrite update_slot_lookup_ne; last done. by apply Hslots.
    - intros k. destruct (decide (k = i)) as [->|k_not_i].
      + rewrite update_slot_lookup Hslots_i /=. split; intros H.
        * exfalso. rewrite Hslots_i in Hval_commit_i.
          destruct si as [γ|γ|]; try by inversion Hval_commit_i.
        * by inversion H.
      + rewrite update_slot_lookup_ne; last done. apply Hstate.
    - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
      + rewrite update_slot_lookup Hslots_i /=. repeat split.
        * rewrite Hslots_i in Hval_commit_i.
          destruct si; try by inversion Hval_commit_i.
        * intros Hi%Hdeqs. destruct Hi as [H _].
          rewrite Hnot_written_i in H. inversion H.
        * by apply Hpref in Hk as (_ & _ & H).
      + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
    - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
      + rewrite update_slot_lookup Hslots_i /update_slot /=.
        rewrite Hslots_i /= insert_delete_insert /array_get lookup_insert.
        rewrite decide_True; last done. repeat split; try done.
        destruct si; try done. rewrite Hslots_i in Hval_commit_i. done.
      + rewrite /array_get update_slot_lookup_ne; last done.
        apply Hdeqs in Hk. rewrite /array_get in Hk. done.
    - destruct (decide (i1 = i)) as [->|Hi1_not_i].
      + rewrite update_slot_lookup Hslots_i /=.
        rewrite Hslots_i in HC4. by inversion HC4.
      + by rewrite update_slot_lookup_ne.
    - destruct (decide (i1 = i)) as [->|Hi1_not_i].
      + rewrite /array_get update_slot_lookup Hslots_i /=.
        destruct (decide (i ∈ deqs)) as [H|H]; last done.
        exfalso. apply Hdeqs in H as (H1 & H2 & H3).
        rewrite Hnot_written_i in H1. inversion H1.
      + by rewrite /array_get update_slot_lookup_ne.
    - destruct (decide (i1 = i)) as [->|Hi1_not_i].
      + rewrite /array_get update_slot_lookup Hslots_i /=.
        rewrite Hslots_i in HC5. inversion HC5; subst wi.
        by rewrite decide_False.
      + rewrite /array_get update_slot_lookup_ne; last done.
        destruct (slots !! i1) as [[[li1 si1] wi1]|]; last by inversion HC4.
        rewrite decide_False; last done. inversion HC5; subst wi1. done. }
  (* There is no [Contra1]/[Contra2], first assume the prophecy is trivial. *)
  destruct bs as [|b blocks].
  { (* We access the atomic update and commit the element. *)
    iMod "AU" as (elts_AU) "[He◯ [_ Hclose]]".
    iDestruct (sync_elts with "He● He◯") as %<-.
    iMod (update_elts _ _ _ (elts ++ [l]) with "He● He◯") as "[He● He◯]".
    iMod ("Hclose" with "[$He◯]") as "HΦ".
    (* We allocate the new slot. *)
    iMod (alloc_done_slot γs slots i l Hi_free with "Hs●")
      as "[Hs [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
    (* And we can close the invariant. *)
    iModIntro. iSplitR "HΦ Hwriting_tok_i".
    { iNext. iExists (S back), pvs, pref, (rest ++ [l]), (NoCont []).
      iExists (<[i := (l, Done, false)]> slots), deqs.
      rewrite array_content_NONEV //. iFrame.
      iFrame. iSplitL "He●".
      { rewrite /elts app_assoc map_get_value_not_in_pref; try done.
        intros Hi%Hpref. rewrite Hi_free in Hi. destruct Hi; done. }
      iSplitL "Hbig Htok_i".
      { iApply big_sepM_insert.
        + apply eq_None_not_Some. intros H. apply Hslots in H. lia.
        + iFrame "Hbig". repeat (iSplit; first done). done. }
      destruct Hcont as (HC1 & HC2 & HC3).
      iPureIntro. repeat split_and; try done; try by lia.
      - intros k. destruct sz as [|sz]; first by lia.
        split; intros Hk.
        + destruct (decide (k = i)) as [->|k_not_i].
          * rewrite lookup_insert. by eexists.
          * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
        + destruct (decide (k = i)) as [->|k_not_i].
          * destruct sz; by lia.
          * rewrite lookup_insert_ne in Hk; last done.
            apply Hslots in Hk.  by lia.
      - intros k. destruct (decide (k = i)) as [->|k_not_i].
        + by rewrite lookup_insert.
        + rewrite lookup_insert_ne; last done. apply Hstate.
      - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
        + by rewrite lookup_insert.
        + rewrite lookup_insert_ne; last done. apply Hpref, Hk.
      - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
        + by rewrite lookup_insert.
        + rewrite /array_get. rewrite lookup_insert_ne; last done.
          apply Hdeqs in Hk as (H1 & H2 & H3). repeat (split; first done).
          rewrite /array_get in H3.
          destruct (slots !! k) as [[[dl ds] dw]|]; last done. done.
      - intros b Hb. by inversion Hb. }
    (* Let's clean up the context a bit. *)
    clear Hslots Hstate Hpref Hdeqs Hcont Hi_not_in_deq Hi_free Hpvs_ND Hpvs_sz.
    clear pvs pref rest slots deqs elts. subst i. rename back into i.
    (* We can now move to the store. *)
    wp_pures. rewrite (bool_decide_true _ Hback_sz).
    wp_pures. wp_bind (_ <- _)%E.
    (* We open the invariant again for the store. *)
    iInv "Inv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[Hℓ_back [Hℓ_ar [Hb● [Hi● [He● [>Hs● HInv]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [>Hcont >Hpures]]]".
    iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
    destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
    (* Using witnesses, we show that our value and state have not changed. *)
    iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
    iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
    iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
    (* Our slot is mapped. *)
    assert (is_Some (slots !! i)) as Hslots_i.
    { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
    (* Our index is in the array. *)
    assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
    (* An we perform the store. *)
    wp_apply (wp_store_offset _ _ ℓ_ar i (array_content sz slots deqs) with "Hℓ_ar").
    { apply array_content_is_Some. by lia. }
    iIntros "Hℓ_ar".
    (* We perform some updates. *)
    iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
    iModIntro. iSplitR "HΦ"; last by wp_pures. iNext.
    (* It remains to re-establish the invariant. *)
    pose (new_slots := update_slot i set_written slots).
    iExists back, pvs, pref, rest, cont, new_slots, deqs.
    subst new_slots. iFrame. iSplitL "Hℓ_ar".
    { rewrite array_content_set_written;
        [ by iFrame | by lia | done | by apply Hstate ]. }
    iSplitL "He●".
    { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
      destruct (decide (k = i)) as [->|Hk_not_i].
      - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
        destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
        inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
      - rewrite update_slot_lookup_ne; last done. done. }
    iSplitL "Hbig".
    { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
      iApply big_sepM_insert; first by rewrite lookup_delete.
      assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
      { rewrite insert_delete_insert. by rewrite insert_id. }
      rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I] HEq_slots.
      iDestruct (big_sepM_insert with "Hbig")
        as "[[H1 [H2 H3]] $]"; first by rewrite lookup_delete.
      rewrite /per_slot_own val_of_set_written state_of_set_written.
      iFrame. by rewrite was_written_set_written. }
    iPureIntro.
    destruct Hslots_i as [[[li si] wi] Hslots_i].
    repeat split_and; try done.
    - intros k. destruct (decide (k = i)) as [->|k_not_i].
      + rewrite update_slot_lookup. split; intros H; last done.
        rewrite Hslots_i. by eexists.
      + rewrite update_slot_lookup_ne; last done. by apply Hslots.
    - intros k. destruct (decide (k = i)) as [->|k_not_i].
      + rewrite update_slot_lookup Hslots_i /=. split; intros H.
        * exfalso. rewrite Hslots_i in Hval_commit_i.
          destruct si as [γ|γ|]; try by inversion Hval_commit_i.
        * by inversion H.
      + rewrite update_slot_lookup_ne; last done. apply Hstate.
    - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
      + rewrite update_slot_lookup Hslots_i /=. repeat split.
        * rewrite Hslots_i in Hval_commit_i.
          destruct si; try by inversion Hval_commit_i.
        * by intros Hi%Hpref.
        * by apply Hpref in Hk as (_ & _ & H).
      + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
    - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
      + rewrite update_slot_lookup Hslots_i /update_slot /=.
        rewrite Hslots_i /= insert_delete_insert /array_get lookup_insert.
        rewrite decide_True; last done. repeat split; try done.
        destruct si; try done. rewrite Hslots_i in Hval_commit_i. done.
      + rewrite /array_get update_slot_lookup_ne; last done.
        apply Hdeqs in Hk. rewrite /array_get in Hk. done.
    - destruct cont as [i1 i2|bs].
      + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6). split; first done.
        destruct (decide (i1 = i)) as [->|Hi1_not_i].
        * rewrite /array_get update_slot_lookup Hslots_i /=.
          repeat split_and; try done.
          ** rewrite Hslots_i in Hval_commit_i. destruct si; try done.
          ** rewrite decide_False; first done. apply Hstate. done.
        * rewrite /array_get update_slot_lookup_ne; last done.
          rewrite /array_get in HC3. done.
      + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
        intros b Hb. apply HC1 in Hb as (Hb1 & Hb2). split.
        * destruct (decide (b.1 = i)) as [Hb1_is_i|Hb1_not_i].
          ** rewrite -Hb1_is_i in Hslots_i. by rewrite Hslots_i in Hb1.
          ** rewrite /update_slot Hslots_i insert_delete_insert.
             by rewrite lookup_insert_ne.
        * intros k Hk. destruct (decide (k = i)) as [Hk_is_i|Hk_not_i].
          ** rewrite /update_slot Hslots_i insert_delete_insert. subst k.
             rewrite lookup_insert /=. rewrite Hslots_i in Hval_commit_i.
             destruct (was_committed (li, si, true)) eqn:H; last done.
             exfalso. apply Hb2 in Hk. rewrite Hslots_i in Hk. inversion Hk.
             destruct si; try done.
          ** rewrite /update_slot Hslots_i insert_delete_insert.
             rewrite lookup_insert_ne; last done. apply Hb2, Hk. }
  (* There is no [Contra1]/[Contra2], and the prophecy is non-trivial. *)
  destruct Hcont as (Hblocks & Hrest & Hpvs).
  assert (rest = []) as -> by by apply Hrest.
  rewrite app_nil_r in elts. rewrite app_nil_r.
  destruct b as [b_unused b_pendings].
  (* We compare our index with the unused element of the prophecy. *)
  destruct (decide (b_unused = i)) as [->|b_unused_not_i].
  + (* We are the non-committed element of the prophecy: commit the block. *)
    (* We allocate the new slot. *)
    iMod (alloc_done_slot γs slots i l Hi_free with "Hs●")
      as "[Hs● [Htok_i [#val_wit_i [#commit_wit_i Hwriting_tok_i]]]]".
    (* We then commit at our index. *)
    iMod "AU" as (elts_AU) "[He◯ [_ Hclose]]".
    iDestruct (sync_elts with "He● He◯") as %<-.
    iMod (update_elts _ _ _ (elts ++ [l]) with "He● He◯") as "[He● He◯]".
    iMod ("Hclose" with "[$He◯]") as "HΦ".
    (* Our prophecy block must be valid. *)
    assert (block_valid slots (i, b_pendings))
      as Hb_valid by apply Hblocks, elem_of_list_here.
    rewrite /block_valid /= in Hb_valid.
    destruct Hb_valid as [Hb_valid1 Hb_valid2].
    (* We also need to commit for all indices in in [p_pendings] *)
    assert (NoDup (i :: b_pendings)) as Hblock_ND.
    { apply NoDup_app in Hpvs_ND as (H & _ & _). subst pvs.
      apply NoDup_app in H as (_ & _ & H). simpl in H.
      rewrite app_comm_cons in H. by apply NoDup_app in H as (H & _ & _). }
    apply NoDup_cons in Hblock_ND as (Hi & HNoDup).
    iAssert (per_slot_own γe γs i (l, Done, false)) with "[Htok_i]" as "Hi".
    { rewrite /per_slot_own /=. eauto with iFrame. }
    iDestruct (big_sepM_insert (per_slot_own γe γs) slots i (l, Done, false)
                 with "[Hi Hbig]") as "Hbig"; [ done | by iFrame | .. ].
    iMod (big_lemma _ _ _ _ b_pendings HNoDup with "Hs● Hbig He●") as "[Hs● [Hbig He●]]".
    { intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
      + exfalso. apply Hi, Hk.
      + rewrite lookup_insert_ne; last done. apply Hb_valid2, Hk. }
    (* And then we can close the invariant. *)
    iModIntro. iSplitR "HΦ Hwriting_tok_i".
    { pose (new_pref := pref ++ i :: b_pendings).
      pose (new_slots := map_imap (helped b_pendings) (<[i:=(l, Done, false)]> slots)).
      iNext. iExists (S back), pvs, new_pref, [], (NoCont blocks), new_slots, deqs.
      iFrame. iSplitL "Hℓ_ar".
      { assert (array_content sz slots deqs = array_content sz new_slots deqs) as ->; last done.
        apply array_content_ext. intros k Hk. rewrite /new_slots /array_get.
        rewrite map_lookup_imap. destruct (decide (k = i)) as [->|Hk_not_i].
        - by rewrite lookup_insert Hb_valid1 /helped /= decide_False.
        - rewrite lookup_insert_ne; last done.
          destruct (slots !! k) as [[[dl ds] dw]|]; last done.
          rewrite /helped /=. destruct ds as [dγ|dγ|].
          + destruct dw; try done; by destruct (decide (k ∈ b_pendings)).
          + by destruct dw.
          + by destruct dw. }
      iSplitL "He●".
      { rewrite app_nil_r /new_pref /elts map_app map_cons.
        rewrite [in get_value new_slots deqs i]/get_value.
        rewrite [in new_slots !! i]/new_slots.
        rewrite map_lookup_imap lookup_insert /= -app_assoc cons_middle.
        assert (NoDup (pref ++ i :: b_pendings)) as HND.
        { apply NoDup_app in Hpvs_ND as (HND & _ & _).
          rewrite cons_middle app_assoc.
          rewrite Hpvs /= in HND. rewrite cons_middle in HND.
          rewrite app_assoc app_assoc in HND.
          by apply NoDup_app in HND as (HND & _ & _). }
        rewrite annoying_lemma_1 //; last first.
        { intros k Hk. by apply Hpref in Hk as (H1 & H2 & _). }
        assert (map (get_value new_slots deqs) b_pendings
              = get_values (<[i:=(l, Done, false)]> slots) b_pendings) as ->.
        - rewrite /new_slots. by eapply annoying_lemma_2.
        - done. }
      iPureIntro. repeat split_and; try done.
      - intros k. rewrite /new_slots map_lookup_imap. split; intros Hk.
        + destruct (decide (k = i)) as [->|Hk_not_i].
          * rewrite lookup_insert /helped /=. by eexists.
          * rewrite lookup_insert_ne; last done.
            assert (is_Some (slots !! k)) as [d ->] by (apply Hslots; lia).
            by apply is_Some_helped.
        + destruct (decide (k = i)) as [->|Hk_not_i]; first by lia.
          rewrite lookup_insert_ne in Hk; last done.
          assert (k < back `min` sz) as H; last by lia.
          apply Hslots. destruct (slots !! k) as [d|]; first by exists d.
          by inversion Hk.
      - intros k. rewrite /new_slots map_lookup_imap.
        destruct (decide (k = i)) as [->|Hk_not_i];
          first by rewrite lookup_insert /helped /=.
        rewrite lookup_insert_ne; last done. split; intros Hk.
        + destruct (slots !! k) as [d|] eqn:HEq; last done.
          assert (was_committed <$> Some d ≫= helped b_pendings k = was_committed <$> Some d) as HEq1.
          { destruct d as [[dl []] dw]; simpl; simpl in Hk; by rewrite Hk. }
          rewrite HEq1 -HEq in Hk. apply Hstate in Hk. rewrite HEq in Hk.
          assert (was_written <$> Some d ≫= helped b_pendings k = was_written <$> Some d) as HEq2.
          { destruct d as [[dl []] []]; simpl; simpl in Hk; try by inversion Hk.
            rewrite /helped /=. destruct (decide (k ∈ b_pendings)); done. }
          rewrite HEq2. by inversion Hk.
        + destruct (slots !! k) as [d|] eqn:HEq; last done.
          assert (was_written <$> Some d ≫= helped b_pendings k = was_written <$> Some d) as HEq1.
          { by destruct d as [[dl []] dw]; rewrite /helped; destruct (decide (k ∈ b_pendings)). }
          rewrite HEq1 -HEq in Hk. apply Hstate in Hk. done.
      - intros k Hk. subst new_pref new_slots. apply elem_of_app in Hk as [Hk|Hk].
        { apply Hpref in Hk as (H1 & H2). split; last done.
          rewrite map_imap_insert /=. destruct (decide (k = i)) as [->|Hk_not_i].
          - by rewrite lookup_insert.
          - rewrite lookup_insert_ne; last done. rewrite map_lookup_imap.
            destruct (slots !! k) as [[[dl ds] dw]|]; last by inversion H1.
            rewrite /= /helped. destruct ds as [dγ|dγ|]; try done. }
        apply elem_of_cons in Hk as [Hk|Hk].
        { subst k. split; last done. by rewrite map_imap_insert /= lookup_insert. }
        apply Hb_valid2 in Hk as Hb_valid2_k. split.
        + rewrite map_lookup_imap. destruct (decide (k = i)) as [->|Hk_not_i].
          * by rewrite lookup_insert /=.
          * rewrite lookup_insert_ne; last done.
            destruct (slots !! k) as [[[kl ks] kw]|]; last by inversion Hb_valid2_k.
            rewrite /= /helped. destruct ks; try done. by rewrite /= decide_True.
        + apply Hstate in Hb_valid2_k. apply Hstate in Hb_valid2_k. done.
      - intros k Hk. subst new_slots. rewrite /array_get map_lookup_imap.
        assert (k ≠ i) as Hk_not_i. { intros ->. apply Hi_not_in_deq, Hk. }
        rewrite lookup_insert_ne; last done. apply Hdeqs in Hk as (H1 & H2 & H3).
        destruct (slots !! k) as [[[lk sk] wk]|] eqn:HEq; last by inversion H1.
        inversion H1; subst wk. rewrite /=. repeat split_and; try by destruct sk.
        destruct sk; try done; simpl.
        + rewrite decide_True; first done.
          rewrite /array_get HEq in H3. simpl in H3.
          destruct (decide (k ∈ deqs)); first done. by inversion H3.
        +  rewrite decide_True; first done.
          rewrite /array_get HEq in H3. simpl in H3.
          destruct (decide (k ∈ deqs)); first done. by inversion H3.
      - intros b Hk. subst new_slots. rewrite map_imap_insert /=.
        assert (b ∈ (i, b_pendings) :: blocks) as H by set_solver +Hk.
        assert (NoDup (i :: b_pendings ++ flatten_blocks blocks)) as HND.
        { subst pvs. apply NoDup_app in Hpvs_ND as (HND & _ & _).
          apply NoDup_app in HND as (_ & _ & HND). done. }
        apply flatten_blocks_mem1 in Hk as Hk1.
        apply Hblocks in H as (H1 & H2). split.
        + assert (b.1 ≠ i) as Hb1_not_i.
          { intros HEq. apply NoDup_cons in HND as [HND1 HND2]. apply HND1.
            rewrite -HEq. apply elem_of_app. by right. }
          rewrite lookup_insert_ne; last done. by rewrite map_lookup_imap H1.
        + intros j Hj. assert (j ≠ i) as Hj_not_i.
          { intros HEq. apply NoDup_cons in HND as [HND1 HND2]. apply HND1.
            rewrite -HEq. apply elem_of_app. right.
            apply (flatten_blocks_mem2 _ _ Hk _ Hj). }
          rewrite lookup_insert_ne; last done. rewrite map_lookup_imap.
          apply H2 in Hj as Hcomm.
          destruct (slots !! j) as [[[lj sj] wj]|]; last by inversion Hj.
          rewrite /= /helped. destruct sj; try done. simpl.
          assert (j ∉ b_pendings); last by rewrite decide_False.
          intros Hj_contra. apply NoDup_cons in HND as [_ HND].
          apply NoDup_app in HND. destruct HND as (HND1 & HND2 & HND3).
          apply (HND2 _ Hj_contra). apply (flatten_blocks_mem2 _ _ Hk _ Hj).
      - by rewrite Hpvs /= /new_pref app_comm_cons app_assoc. }
    clear Hslots Hstate Hpref Hdeqs Hpvs Hrest Hblocks Hi_free Hi_not_in_deq.
    clear Hpvs_ND Hpvs_sz Hb_valid1 Hb_valid2 HNoDup Hi elts pvs pref slots deqs.
    clear blocks b_pendings. subst i. rename back into i.
    wp_pures. rewrite bool_decide_true; last done. wp_pures.
    wp_bind (_ <- _)%E.
    (* We open the invariant again for the store. *)
    iInv "Inv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[Hℓ_back [Hℓ_ar [Hb● [Hi● [He● [>Hs● HInv]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [>Hcont >Hpures]]]".
    iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
    destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
    (* Using witnesses, we show that our value and state have not changed. *)
    iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
    iDestruct (use_committed_wit with "Hs● commit_wit_i") as %Hval_commit_i.
    iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
    (* Our slot is mapped. *)
    assert (is_Some (slots !! i)) as Hslots_i.
    { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
    (* Our index is in the array. *)
    assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
    (* An we perform the store. *)
    wp_apply (wp_store_offset _ _ ℓ_ar i (array_content sz slots deqs) with "Hℓ_ar").
    { apply array_content_is_Some. by lia. }
    iIntros "Hℓ_ar".
    (* We perform some updates. *)
    iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
    iModIntro. iSplitR "HΦ"; last by wp_pures. iNext.
    (* It remains to re-establish the invariant. *)
    { pose (new_slots := update_slot i set_written slots).
      iExists back, pvs, pref, rest, cont, new_slots, deqs.
      subst new_slots. iFrame. iSplitL "Hℓ_ar".
      { rewrite array_content_set_written;
          [ by iFrame | by lia | done | by apply Hstate ]. }
      iSplitL "He●".
      { erewrite map_ext; first by iFrame. rewrite /get_value. intros k.
        destruct (decide (k = i)) as [->|Hk_not_i].
        - rewrite update_slot_lookup. destruct Hslots_i as [d Hslots_i].
          destruct d as [[ld sd] wd]. rewrite Hslots_i in Hnot_written_i.
          inversion Hnot_written_i; subst wd. rewrite Hslots_i /=. done.
        - rewrite update_slot_lookup_ne; last done. done. }
      iSplitL "Hbig".
      { rewrite /update_slot. destruct (slots !! i) as [d|] eqn:HEq; last done.
        iApply big_sepM_insert; first by rewrite lookup_delete.
        assert (slots = <[i:=d]> (delete i slots)) as HEq_slots.
        { rewrite insert_delete_insert. by rewrite insert_id. }
        rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I] HEq_slots.
        iDestruct (big_sepM_insert with "Hbig")
          as "[[H1 [H2 H3]] $]"; first by rewrite lookup_delete.
        rewrite /per_slot_own val_of_set_written state_of_set_written.
        iFrame. by rewrite was_written_set_written. }
      iPureIntro.
      repeat split_and; try done.
      - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
        + rewrite update_slot_lookup. split; intros Hk; last by lia.
          by apply fmap_is_Some.
        + rewrite update_slot_lookup_ne; last done. apply Hslots.
      - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
        + rewrite update_slot_lookup. split; intros Hk; exfalso.
          * destruct (slots !! i) as [[[li si] wi]|]; last by inversion Hk.
            inversion_clear Hnot_written_i. destruct si; inversion Hk.
            inversion Hval_commit_i.
          * destruct (slots !! i) as [[[li si] wi]|]; by inversion Hk.
        + rewrite update_slot_lookup_ne; last done. by apply Hstate.
      - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
        + rewrite update_slot_lookup /=. split.
          * destruct (slots !! i) as [[[li si] wi]|]; first done.
            by inversion Hval_wit_i.
          * apply Hpref, Hk.
        + rewrite update_slot_lookup_ne; last done. by apply Hpref.
      - intros k Hk. assert (k ≠ i) as Hk_not_i.
        { intros ->. apply Hdeqs in Hk as (H1 & H2 & H3).
          apply Hstate in Hnot_written_i. rewrite /array_get in H3.
          destruct Hslots_i as [[[li si] wi] Hslots_i].
          rewrite Hslots_i decide_False in H3; last done.
          rewrite Hslots_i in H1. inversion H1; subst wi. inversion H3. }
        rewrite /array_get update_slot_lookup_ne; last done.
        apply Hdeqs in Hk. rewrite /array_get in Hk. done.
      - destruct cont as [i1 i2|bs].
        + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6).
          split; first done. repeat split_and; try done.
          * destruct (decide (i1 = i)) as [->|Hi1_not_i].
            ** rewrite update_slot_lookup.
               destruct (slots !! i) as [[[li si] wi]|]; first done.
               by inversion Hval_wit_i.
            ** by rewrite update_slot_lookup_ne.
          * destruct (decide (i1 = i)) as [->|Hi1_not_i].
            ** rewrite /array_get update_slot_lookup.
               destruct (slots !! i) as [[[li si] wi]|] eqn:HEq; try done.
            ** by rewrite /array_get update_slot_lookup_ne.
          * destruct (decide (i1 = i)) as [->|Hi1_not_i].
            ** rewrite /array_get update_slot_lookup.
               destruct (slots !! i) as [[[li si] wi]|] eqn:HEq; try done.
               inversion  HC3; subst wi. done.
            ** rewrite /array_get update_slot_lookup_ne; last done.
               destruct (slots !! i1) as [[[li1 si1] wi1]|] eqn:HEq; try done.
               rewrite decide_False; last done. inversion HC3; subst wi1. done.
        + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
          destruct Hslots_i as [[[li si] wi] Hslots_i].
          intros b Hb. apply HC1 in Hb as (Hb1 & Hb2). split.
          * destruct (decide (b.1 = i)) as [Hb1_is_i|Hb1_not_i].
            ** rewrite -Hb1_is_i in Hslots_i. rewrite Hb1 in Hslots_i.
               by inversion Hslots_i.
            ** by rewrite /update_slot Hslots_i insert_delete_insert lookup_insert_ne.
          * intros k Hk. destruct (decide (k = i)) as [Hk_is_i|Hk_not_i].
            ** rewrite /update_slot Hslots_i insert_delete_insert. subst k.
               rewrite lookup_insert /=. rewrite Hslots_i in Hval_commit_i.
               destruct (was_committed (li, si, true)) eqn:H; last done.
               exfalso. apply Hb2 in Hk. rewrite Hslots_i in Hk. inversion Hk.
               destruct si; try done.
            ** rewrite /update_slot Hslots_i insert_delete_insert.
               rewrite lookup_insert_ne; last done. apply Hb2, Hk. }
  + (* We are not the first non-done element, we will give away our AU. *)
    iMod (saved_prop_alloc (Φ #())) as (γs_i) "#Hγs_i"; first done.
    iMod (alloc_pend_slot γs slots i l γs_i Hi_free with "Hs●")
      as "[Hs● [Htok_i [#val_wit_i [Hpend_tok_i [Hname_tok_i Hwriting_tok_i]]]]]".
    (* We close the invariant, storing our AU. *)
    iModIntro. iSplitR "Htok_i Hname_tok_i Hwriting_tok_i".
    { pose (new_bs := glue_blocks (b_unused, b_pendings) i blocks).
      pose (new_slots := <[i:=(l, Pend γs_i, false)]> slots).
      iNext. iExists (S back), pvs, pref, [], (NoCont new_bs), new_slots, deqs.
      rewrite app_nil_r. iFrame. iSplitL "Hℓ_ar".
      { assert (array_content sz slots deqs = array_content sz new_slots deqs) as ->; last done.
        apply array_content_ext. intros k Hk. rewrite /new_slots /array_get.
        destruct (decide (k = i)) as [->|Hk_not_i].
        - by rewrite Hi_free lookup_insert decide_False.
        - rewrite lookup_insert_ne; last done. destruct (slots !! k) as [d|]; last done.
          destruct d as [[dl ds] dw]. rewrite /helped /=.
          destruct ds as [dγ|dγ|]; destruct dw; try done. }
      iSplitL "He●".
      { erewrite map_ext_in; first done. subst new_slots.
        intros k Hk%elem_of_list_In. rewrite /get_value.
        assert (k ≠ i); last by rewrite lookup_insert_ne.
        intros ->. apply Hpref in Hk as (H1 & H2).
        rewrite Hi_free in H1. inversion H1. }
      iSplitL "Hbig Hpend_tok_i AU".
      { iApply big_sepM_insert; first done. iFrame "#∗". }
      iPureIntro. subst new_slots. repeat split_and; try done.
      - intros k. destruct sz as [|sz]; first by lia.
        split; intros Hk.
        + destruct (decide (k = i)) as [->|k_not_i].
          * rewrite lookup_insert. by eexists.
          * rewrite lookup_insert_ne; last done. apply Hslots. by lia.
        + destruct (decide (k = i)) as [->|k_not_i].
          * destruct sz; by lia.
          * rewrite lookup_insert_ne in Hk; last done.
            apply Hslots in Hk.  by lia.
      - intros k. destruct (decide (k = i)) as [->|Hk_not_i].
        + by rewrite lookup_insert.
        + rewrite lookup_insert_ne; last done. apply Hstate.
      - intros k Hk. rewrite lookup_insert_ne; first by apply Hpref, Hk.
        intros HEq. subst k. apply Hpref in Hk as [H _].
        rewrite Hi_free in H. inversion H.
      - intros k Hk. rewrite /array_get lookup_insert_ne.
        + apply Hdeqs in Hk. by rewrite /array_get in Hk.
        + intros <-. apply Hdeqs in Hk as [Hk _]. rewrite Hi_free in Hk. done.
      - intros b Hb. subst new_bs. rewrite Hpvs in Hpvs_ND.
        apply NoDup_app in Hpvs_ND as (HND & _ & _).
        apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
        by eapply glue_blocks_valid.
      - subst pvs new_bs. f_equal. apply flatten_blocks_glue. }
    clear Hslots Hstate Hpref Hdeqs Hblocks Hrest Hpvs Hi_free Hi_not_in_deq.
    clear Hpvs_ND Hpvs_sz b_unused b_unused_not_i elts blocks pvs pref slots.
    clear deqs b_pendings. subst i. rename back into i.
    wp_pures. rewrite bool_decide_true; last done.
    wp_pures. wp_bind (_ <- _)%E.
    (* We open the invariant again for the store. *)
    iInv "Inv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[Hℓ_back [Hℓ_ar [Hb● [Hi● [He● [>Hs● HInv]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [>Hcont >Hpures]]]".
    iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
    destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
    (* Using witnesses, we show that our value and state have not changed. *)
    iDestruct (use_val_wit with "Hs● val_wit_i") as %Hval_wit_i.
    iDestruct (writing_tok_not_written with "Hs● Hwriting_tok_i") as %Hnot_written_i.
    (* Our slot is mapped. *)
    assert (is_Some (slots !! i)) as Hslots_i.
    { destruct (slots !! i) as [d|]; first by exists d. inversion Hval_wit_i. }
    (* Our index is in the array. *)
    assert (i < back `min` sz) as Hi_le_back by by apply Hslots.
    (* An we perform the store. *)
    wp_apply (wp_store_offset _ _ ℓ_ar i (array_content sz slots deqs) with "Hℓ_ar").
    { apply array_content_is_Some. by lia. }
    iIntros "Hℓ_ar".
    (* We now look at the state of our cell. *)
    destruct Hslots_i as [[[l' s] w] Hi].
    rewrite Hi in Hval_wit_i. simpl in Hval_wit_i.
    inversion Hval_wit_i; subst l'.
    destruct s as [γs_i'|γs_i'|].
    - (* We are still in the pending state: contradiction. *)
      (* We need to run our atomic update ourselves, we recover it. *)
      rewrite -[in X in ([∗ map] _ ↦ _ ∈ X, _)%I](insert_id _ _ _ Hi).
      rewrite -insert_delete_insert.
      iDestruct (big_sepM_insert with "Hbig")
        as "[Hbig_i Hbig]"; first by apply lookup_delete.
      iDestruct "Hbig_i" as "[_ [_ [Hcommit_tok_i HAU]]]".
      iDestruct "HAU" as (Q) "[Hsaved AU]".
      (* We use the name token to show that γs_i and γs_i' are equal. *)
      iDestruct (use_name_tok with "Hs● Hname_tok_i") as %Hname_tok_i.
      assert (γs_i' = γs_i) as Hγs_i; last subst γs_i'.
      { rewrite Hi /= in Hname_tok_i. by inversion Hname_tok_i. }
      iDestruct (saved_prop_agree with "Hγs_i Hsaved") as "HQ_is_Φ".
      (* We run our atomic update ourself. *)
      pose (elts := map (get_value slots deqs) pref ++ rest).
      iMod "AU" as (elts_AU) "[He◯ [_ Hclose]]".
      iDestruct (sync_elts with "He● He◯") as %<-.
      iMod (update_elts _ _ _ (elts ++ [l]) with "He● He◯") as "[He● He◯]".
      iMod ("Hclose" with "[$He◯]") as "HΦ".
      iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
      iMod (use_pending_tok with "Hs● Hcommit_tok_i") as "[Hs● #commit_wit_i]".
      { by rewrite update_slot_lookup Hi /=. }
      iMod (helped_to_done with "Hs● Hname_tok_i") as "Hs●".
      { by rewrite update_slot_lookup update_slot_lookup Hi. }
      (* We now act according ot the contradiction status. *)
      destruct cont as [i1 i2|bs].
      * (* A contradiction has arised from somewhere else, we keep it. *)
        iModIntro. iSplitR "HQ_is_Φ HΦ".
        { iNext. iExists back, pvs, pref, (rest ++ [l]), (WithCont i1 i2).
          iExists (update_slot i set_written_and_done slots), deqs.
          subst elts. rewrite app_assoc. iFrame. iSplitL "Hℓ_ar".
          { rewrite array_content_set_written_and_done;
            [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
          iSplitL "He●".
          { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
            rewrite /get_value /update_slot Hi insert_delete_insert.
            destruct (decide (k = i)) as [->|Hk_not_i].
            - by rewrite lookup_insert Hi.
            - by rewrite lookup_insert_ne. }
          iSplitL "Hs●".
          { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
          iSplitL.
          {  rewrite /update_slot Hi.
            iApply big_sepM_insert; first by rewrite lookup_delete.
            iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
            iSplit; first done. iSplit; done. }
          iPureIntro.
          destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
          repeat split_and; try lia; try done.
          - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
            + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
            + rewrite update_slot_lookup_ne; last done. apply Hslots.
          - intros k. split; intros Hk.
            + assert (k ≠ i) as Hk_not_i.
              { intros ->. by rewrite update_slot_lookup Hi in Hk. }
              rewrite update_slot_lookup_ne; last done.
              rewrite update_slot_lookup_ne in Hk; last done.
              by apply Hstate.
            + assert (k ≠ i) as Hk_not_i.
              { intros ->. by rewrite update_slot_lookup Hi in Hk. }
              rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
          - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
            + rewrite update_slot_lookup Hi /=. split; [ done | by apply Hpref, Hk ].
            + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
          - intros k Hk. assert (k ≠ i) as Hk_not_i.
            { intros ->. apply Hdeqs in Hk as (H1 & H2 & H3).
              apply Hstate in Hnot_written_i. rewrite /array_get in H3.
              rewrite Hi decide_False in H3; last done.
              rewrite Hi in H1. inversion H1; subst w. inversion H3. }
            rewrite /array_get update_slot_lookup_ne; last done.
            apply Hdeqs in Hk. rewrite /array_get in Hk. done.
          - destruct (decide (i1 = i)) as [->|Hi1_not_i].
            + by rewrite update_slot_lookup Hi.
            + by rewrite update_slot_lookup_ne.
          - destruct (decide (i1 = i)) as [->|Hi1_not_i].
            + by rewrite update_slot_lookup Hi /=.
            + rewrite update_slot_lookup_ne; last done.
              destruct (slots !! i1) as [[[li1 si1] wi1]|]; last by inversion HC4.
              inversion HC5; subst wi1. done.
          - destruct (decide (i1 = i)) as [->|Hi1_not_i].
            + by rewrite /array_get update_slot_lookup Hi /= decide_False.
            + rewrite /array_get update_slot_lookup_ne; last done.
              destruct (slots !! i1) as [[[li1 si1] wi1]|]; last by inversion HC4.
              rewrite decide_False; last done. inversion HC5; subst wi1. done. }
        wp_pures. iRewrite "HQ_is_Φ". done.
      * (* No contradiction yet, make it ours if the prophecy is non-trivial. *)
        iAssert (match bs with
                 | [] => i2_lower_bound γi (back `min` sz)
                 | _  => no_contra γc ∗ i2_lower_bound γi (back `min` sz)
                 end -∗ |==>
                   match bs with
                   | []           => True
                   | (i2, _) :: _ => contra γc i i2
                   end ∗
                   match bs with
                   | []           => i2_lower_bound γi (back `min` sz)
                   | (i2, _) :: _ => i2_lower_bound γi i2
                   end)%I as "Hup".
        { destruct bs as [|[i2 ps] bs]; first (iIntros "Hi●"; by iFrame).
          iIntros "[Hcont Hi●]". iMod (to_contra i i2 with "Hcont") as "$".
          iMod (i2_lower_bound_update _ _ i2 with "Hi●") as "$"; last done.
          assert (block_valid slots (i2, ps)) as [Hvalid _].
          { destruct Hcont as (Hblocks & _ & _). apply Hblocks, elem_of_list_here. }
          assert (¬ (i2 < back `min` sz)) as H%not_lt; last by lia.
          eapply iffRLn.
          - apply Hslots.
          - intros H. rewrite Hvalid in H. by inversion H. }
        iAssert (match bs with
                 | [] => i2_lower_bound γi (back `min` sz)
                 | _  => no_contra γc ∗ i2_lower_bound γi (back `min` sz)
                 end ∗
                 match bs with
                 | [] => no_contra γc
                 | _  => True
                 end)%I with "[Hcont Hi●]" as "[HNC_triv HNC_non_triv]".
        { destruct bs; by iFrame. }
        iMod ("Hup" with "HNC_triv") as "[#HC_triv Hi●]".
        (* We can now close the invariant. *)
        iModIntro. iSplitR "HQ_is_Φ HΦ".
        { pose (new_slots := update_slot i set_written_and_done slots).
          pose (cont := match bs with [] => NoCont [] | (i2, _) :: _ => WithCont i i2 end).
          iNext. iExists back, pvs, pref, (rest ++ [l]), cont, new_slots, deqs.
          subst new_slots elts cont. rewrite app_assoc. iFrame. iSplitL "Hℓ_ar".
          { rewrite array_content_set_written_and_done;
            [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
          iSplitL "Hi●".
          { destruct bs as [|[b_u b_ps] bs]; by iFrame. }
          iSplitL "He●".
          { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
            rewrite /get_value /update_slot Hi insert_delete_insert.
            destruct (decide (k = i)) as [->|Hk_not_i].
            - by rewrite lookup_insert Hi.
            - by rewrite lookup_insert_ne. }
          iSplitL "Hs●".
          { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
          iSplitR "HNC_non_triv".
          { rewrite /update_slot Hi.
            iApply big_sepM_insert; first by rewrite lookup_delete.
            iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
            iSplit; first done. iSplit; done. }
          iSplitL "HNC_non_triv"; first by destruct bs as [|[i2 ps] bs].
          iPureIntro. repeat split_and.
          - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
            + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
            + rewrite update_slot_lookup_ne; last done. apply Hslots.
          - intros k. split; intros Hk.
            + assert (k ≠ i) as Hk_not_i.
              { intros ->. by rewrite update_slot_lookup Hi in Hk. }
              rewrite update_slot_lookup_ne; last done.
              rewrite update_slot_lookup_ne in Hk; last done.
              by apply Hstate.
            + assert (k ≠ i) as Hk_not_i.
              { intros ->. by rewrite update_slot_lookup Hi in Hk. }
              rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
          - intros k Hk. apply Hpref in Hk as (H1 & H2 & _). repeat split; try done.
            + destruct (decide (k = i)) as [->|Hk_not_i].
              * by rewrite update_slot_lookup Hi.
              * by rewrite update_slot_lookup_ne.
            + destruct bs as [|[b_u b_ps] bs]; first done.
              intros ->. rewrite Hi in H1. by inversion H1.
          - intros k Hk. assert (k ≠ i) as Hk_not_i.
            { intros ->. apply Hdeqs in Hk as (H1 & H2 & H3).
              apply Hstate in Hnot_written_i. rewrite /array_get in H3.
              rewrite Hi decide_False in H3; last done.
              rewrite Hi in H1. inversion H1; subst w. inversion H3. }
            rewrite /array_get update_slot_lookup_ne; last done.
            apply Hdeqs in Hk. rewrite /array_get in Hk. done.
          - done.
          - done.
          - destruct Hcont as (HC1 & HC2 & HC3).
            destruct bs as [|[i2 ps] bs].
            + repeat split_and; try done. intros. by set_solver.
            + repeat split_and; try lia.
              * assert (i < back `min` sz)
                  as Hi_lt by (apply Hslots; by eexists).
                assert (block_valid slots (i2, ps))
                  as Hvalid by apply HC1, elem_of_list_here.
                assert (slots !! i2 = None)
                  as Hi2_None by by destruct Hvalid as (H & _).
                assert (¬ i2 < back `min` sz) as Hi2_ge; last by lia.
                intros H%Hslots. rewrite Hi2_None in H. by inversion H.
              * apply Hpvs_sz. subst pvs. apply elem_of_app. right. simpl.
                by apply elem_of_list_here.
              * by rewrite update_slot_lookup Hi /=.
              * by rewrite update_slot_lookup Hi /=.
              * by apply Hstate.
              * rewrite /array_get update_slot_lookup Hi /=.
                rewrite decide_False; first done. apply Hstate. done.
              * rewrite HC3 /=. exists (ps ++ flatten_blocks bs).
                by rewrite cons_middle app_assoc. }
        wp_pures. iRewrite "HQ_is_Φ". done.
    - (* We have moved to the helped state. *)
      assert (slots = <[i := (l, Help γs_i', w)]> (delete i slots))
        as Hslots_i by by rewrite insert_delete_insert insert_id.
      rewrite [X in ([∗ map] _ ↦ _ ∈ X, _)%I]Hslots_i.
      (* We recover our postcondition. *)
      iDestruct (big_sepM_insert with "Hbig")
        as "[Hbig_i Hbig]"; first by apply lookup_delete.
      iDestruct "Hbig_i" as "[_ [_ [Hcommit_wit_i Hpost]]]".
      iDestruct "Hpost" as (Q) "[Hsaved Hpost]".
      (* We use the name token to show that γs_i and γs_i' are equal. *)
      iDestruct (use_name_tok with "Hs● Hname_tok_i") as %Hname_tok_i.
      assert (γs_i' = γs_i) as Hγs_i; last subst γs_i'.
      { rewrite Hi /= in Hname_tok_i. by inversion Hname_tok_i. }
      iDestruct (saved_prop_agree with "Hγs_i Hsaved") as "HQ_is_Φ".
      (* We need to move from helped to done. *)
      iMod (helped_to_done with "Hs● Hname_tok_i") as "Hs●". { by rewrite Hi. }
      (* We perform some updates. *)
      iMod (use_writing_tok with "Hs● Hwriting_tok_i") as "[Hs● #written_wit_i]".
      iModIntro. iSplitR "HQ_is_Φ Hpost".
      { pose (new_slots := update_slot i set_written_and_done slots).
        iNext. iExists back, pvs, pref, rest, cont, new_slots, deqs.
        subst new_slots. iFrame. iSplitL "Hℓ_ar".
        { rewrite array_content_set_written_and_done;
            [ by iFrame | by lia | by rewrite Hi | by apply Hstate ]. }
      iSplitL "He●".
      { erewrite map_ext_in; first done. intros k Hk%elem_of_list_In.
        rewrite /get_value /update_slot Hi insert_delete_insert.
        destruct (decide (k = i)) as [->|Hk_not_i].
        - by rewrite lookup_insert Hi.
        - by rewrite lookup_insert_ne. }
      iSplitL "Hs●".
      { repeat rewrite update_slot_update_slot. by rewrite /update_slot Hi. }
      iSplitL.
      { rewrite /update_slot Hi.
        iApply big_sepM_insert; first by rewrite lookup_delete.
        iFrame "Hbig". rewrite /per_slot_own /=. iFrame. iSplit; done. }
      iPureIntro. repeat split_and; try done.
      - intros k. destruct (decide (i = k)) as [->|Hk_not_i].
        + rewrite update_slot_lookup Hi. split; [ by eexists | lia ].
        + rewrite update_slot_lookup_ne; last done. apply Hslots.
      - intros k. split; intros Hk.
        + assert (k ≠ i) as Hk_not_i.
          { intros ->. by rewrite update_slot_lookup Hi in Hk. }
          rewrite update_slot_lookup_ne; last done.
          rewrite update_slot_lookup_ne in Hk; last done.
          by apply Hstate.
        + assert (k ≠ i) as Hk_not_i.
          { intros ->. by rewrite update_slot_lookup Hi in Hk. }
          rewrite update_slot_lookup_ne in Hk; last done. by apply Hstate.
      - intros k Hk. destruct (decide (k = i)) as [->|Hk_not_i].
        + rewrite update_slot_lookup Hi. split; first done. apply Hpref, Hk.
        + rewrite update_slot_lookup_ne; last done. apply Hpref, Hk.
      - intros k Hk. assert (k ≠ i) as Hk_not_i.
        { intros ->. apply Hdeqs in Hk as (H1 & H2 & H3).
          apply Hstate in Hnot_written_i. rewrite /array_get in H3.
          rewrite Hi decide_False in H3; last done.
          rewrite Hi in H1. inversion H1; subst w. inversion H3. }
        rewrite /array_get update_slot_lookup_ne; last done.
        apply Hdeqs in Hk. rewrite /array_get in Hk. done.
      - destruct cont as [i1 i2|bs].
        + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6).
          split; first done. repeat split_and; try done.
          * destruct (decide (i1 = i)) as [->|Hi1_not_i].
            ** by rewrite update_slot_lookup Hi.
            ** by rewrite update_slot_lookup_ne.
          * destruct (decide (i1 = i)) as [->|Hi1_not_i].
            ** by rewrite /array_get update_slot_lookup Hi /=.
            ** rewrite /array_get update_slot_lookup_ne; last done.
               rewrite /array_get in HC3. done.
          * destruct (decide (i1 = i)) as [->|Hi1_not_i].
            ** by rewrite /array_get update_slot_lookup Hi decide_False.
            ** rewrite /array_get update_slot_lookup_ne; last done.
               rewrite /array_get in HC3. done.
        + destruct Hcont as (HC1 & HC2 & HC3). repeat split_and; try done.
          intros b Hb. apply HC1 in Hb as (H1 & H2). split.
          ** assert (b.1 ≠ i) as Hb1_not_i.
             { intros H. rewrite H in H1. by rewrite Hi in H1. }
             by rewrite update_slot_lookup_ne.
          ** intros k Hk. assert (k ≠ i) as Hb1_not_i.
             { intros H. subst k. apply H2 in Hk. rewrite Hi in Hk.
               by inversion Hk. }
             rewrite update_slot_lookup_ne; last done. by apply H2. }
      wp_pures. iRewrite "HQ_is_Φ". done.
    - (* We are in the done state: contradiction. *)
      iDestruct (big_sepM_lookup _ _ i with "Hbig")
        as "[_ [_ H]]"; first done; simpl.
      iDestruct "H" as "[_ Htok_i']".
      by iDestruct (slot_token_exclusive with "Htok_i Htok_i'") as "H".
Qed.

Lemma dequeue_spec sz γe (q : val) :
  is_hwq sz γe q -∗
  <<{ ∀∀ (ls : list loc), hwq_cont γe ls }>>
    dequeue q @ ↑N
  <<{ ∃∃ (l : loc) ls', ⌜ls = l :: ls'⌝ ∗ hwq_cont γe ls' | RET #l }>>.
Proof.
  iIntros "Hq" (Φ) "AU". iLöb as "IH".
  iDestruct "Hq" as (γb γi γc γs ℓ_ar ℓ_back p ->) "#Inv".
  wp_lam. wp_pures. wp_bind (! _)%E.
  (* We need to open the invariant to read [q.back]. *)
  iInv "Inv" as (back pvs pref rest cont slots deqs) "HInv".
  iDestruct "HInv" as "[Hℓ_back [Hℓ_ar [>Hb● [Hi● [He● [Hs● HInv]]]]]]".
  iDestruct "HInv" as "[Hproph [Hbig [>Hcont Hpures]]]". wp_load.
  (* If there is a contradiction, remember that. *)
  iAssert (match cont with
           | NoCont _       => True
           | WithCont i1 i2 => contra γc i1 i2
           end)%I with "[Hcont]" as "#Hinit_cont".
  { destruct cont as [i1 i2|bs]; [ by iDestruct "Hcont" as "#C" | done ]. }
  (* We remember the current back value. *)
  iMod (back_snapshot with "Hb●") as "[Hb● Hback_snap]".
  iMod (i2_lower_bound_snapshot with "Hi●") as "[Hi● Hi2_lower_bound]".
  (* We close the invariant again. *)
  iModIntro. iSplitR "AU Hback_snap Hi2_lower_bound".
  { iNext. repeat iExists _. eauto with iFrame. }
  clear pref rest slots deqs pvs.
  (* The range is the min between [q.back - 1] and [q.size - 1]. *)
  wp_bind (minimum _ _)%E. wp_apply minimum_spec_nat. wp_pures.
  (* We now prove the inner loop part by induction in the index. *)
  assert (back `min` sz ≤ back `min` sz) as Hn by done.
  assert (match cont with
          | NoCont _      => True
          | WithCont i1 _ => back `min` sz - back `min` sz ≤ i1
          end) as Hcont_i1 by (destruct cont as [i1 _|_]; lia).
  revert Hn Hcont_i1. generalize (back `min` sz) at 1 4 7 as n.
  intros n Hn Hcont_i1.
  iInduction n as [|n] "IH_loop" forall (Hn Hcont_i1).
  (* The bas case is trivial. *)
  { wp_lam. wp_pures. iApply "IH"; last done.
    iExists _, _, _, _, _, _, _. iSplitR; done. }
  (* Now the induction case: we need to open the invariant for the load. *)
  wp_lam. wp_pures. wp_bind (! _)%E.
  iInv "Inv" as (back' pvs pref rest cont' slots deqs) "HInv".
  iDestruct "HInv" as "[Hℓ_back [Hℓ_ar [>Hb● [Hi● [He● [Hs● HInv]]]]]]".
  iDestruct "HInv" as "[Hproph [Hbig [Hcont >Hpures]]]".
  iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
  destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
  (* We use our snapshot to show that back is smaller that back'. *)
  iDestruct (back_le with "Hb● Hback_snap") as %Hback.
  (* We define the loop index as [i]. *)
  pose (i := (back `min` sz) - S n).
  assert ((back `min` sz)%nat - S n = i)%Z as -> by by rewrite Nat2Z.inj_sub.
  (* We can now load. *)
  wp_apply (wp_load_offset _ _ ℓ_ar _ i _ (array_get slots deqs i) with "Hℓ_ar");
    [ apply array_content_lookup; lia | ]. iIntros "Hℓa".
  (* If there was an initial contradiction, it is still here. *)
  iAssert ⌜match cont with
           | NoCont _       => True
           | WithCont i1 i2 => cont' = cont ∧ (back `min` sz - S n ≤ i1)
           end⌝%I as %Hinitial_cont.
  { destruct cont as [i1 i2|bs]; destruct cont' as [i1' i2'|bs']; try done.
    - iDestruct (contra_agree with "Hinit_cont Hcont") as %[-> ->].
      iPureIntro. split; first done.
      destruct Hcont as (((H1 & H2) & H3) & _). lia.
    - by iDestruct (contra_not_no_contra with "Hcont Hinit_cont") as "False". }
  (* We then reason by cas on the physical contents of slot [i]. *)
  destruct (decide (array_get slots deqs i = NONEV)) as [Hi_NULL|Hi_not_NULL].
  { rewrite Hi_NULL. iModIntro.
    iSplitR "AU Hback_snap Hi2_lower_bound".
    { iNext. repeat iExists _. iFrame. iSplit; done. }
    wp_pures. assert (S n - 1 = n)%Z as -> by lia.
    iApply ("IH_loop" with "[] [] AU Hback_snap").
    - iPureIntro. lia.
    - iPureIntro. destruct cont as [i1 i2|bs]; last done.
       destruct Hinitial_cont as [-> Hi1].
       destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6).
       apply Nat.lt_eq_cases in Hcont_i1 as [H|H]; rewrite -/i in H; first by lia.
       exfalso. subst i1.
       assert (is_Some (slots !! i)) as [d Hslots_i] by (apply Hslots; lia).
       destruct d as [[li si] wi]. rewrite /array_get Hslots_i /= in Hi_NULL.
       rewrite /array_get Hslots_i in HC3. rewrite decide_False in Hi_NULL; last done.
       inversion HC3; subst wi. by inversion Hi_NULL.
    - by iFrame. }
  (* We know that a non-null value [li] at index [i], we get a witness. *)
  assert (is_Some (slots !! i)) as [[[li si] wi] Hslots_i].
  { rewrite /array_get in Hi_not_NULL.
    destruct (slots !! i) as [d|]; last done. by eexists. }
  assert (array_get slots deqs i = SOMEV #li) as ->.
  { rewrite /array_get Hslots_i /=. rewrite /array_get Hslots_i in Hi_not_NULL.
    revert Hi_not_NULL. destruct (decide (i ∈ deqs)); intros H; first done.
    by destruct wi. }
  iMod (val_wit_from_auth γs i li with "Hs●")
    as "[Hs● #Hval_wit_i]"; first by rewrite Hslots_i.
  (* Close the invariant and clean up the context. *)
  iModIntro. iSplitR "AU Hback_snap Hi2_lower_bound".
  { iNext. repeat iExists _. iFrame. iSplit; done. }
  clear Hslots Hstate Hpref Hdeqs Hcont Hinitial_cont Hback back' Hpvs_ND.
  clear Hpvs_sz pvs pref rest cont' Hslots_i si wi Hi_not_NULL slots deqs.
  (* Finally, the interesting where the cell was non-NULL on the load. *)
  wp_pures. wp_bind (Resolve _ _ _)%E.
  iInv "Inv" as (back' pvs pref rest cont' slots deqs) "HInv".
  iDestruct "HInv" as "[Hℓ_back [Hℓ_ar [>Hb● [>Hi● [He● [>Hs● HInv]]]]]]".
  iDestruct "HInv" as "[>Hproph [Hbig [>Hcont >Hpures]]]".
  iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont).
  destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
  (* If there was an initial contradiction, it is still here. *)
  iAssert ⌜match cont with
           | NoCont _       => True
           | WithCont i1 i2 => cont' = cont ∧ back `min` sz - S n ≤ i1
           end⌝%I as %Hinitial_cont.
  { destruct cont as [i1 i2|bs]; destruct cont' as [i1' i2'|bs']; try done.
    - iDestruct (contra_agree with "Hinit_cont Hcont") as %[-> ->].
      iPureIntro. split; first done. destruct Hcont as (((H1 & H2) & H3) & _). done.
    - by iDestruct (contra_not_no_contra with "Hcont Hinit_cont") as "False". }
  (* We resolve. *)
  iDestruct "Hproph" as (rs) "[Hp Hpvs]". iDestruct "Hpvs" as %Hpvs.
  wp_apply (wp_resolve with "Hp"); first done.
  (* We reason by case on the success of the CAS. *)
  iDestruct (array_contents_cases γs slots deqs with "Hs● Hval_wit_i") as %[Hi|Hi].
  * (* The CmpXchg succeeded. *) iClear "IH_loop IH".
    assert (array_content sz slots deqs !! i = Some (SOMEV #li)).
    { rewrite array_content_lookup; last by lia. by rewrite Hi. }
    wp_apply (wp_cmpxchg_suc_offset with "Hℓ_ar");
      [ done | done | by right | ]. iIntros "Hℓ_ar" (rs' ->) "Hp".
    (* Note that [i] is used (otherwise the CmpXchg would have failed). *)
    iDestruct (use_val_wit with "Hs● Hval_wit_i") as %Hval_wit_i.
    iDestruct (back_le with "Hi● Hi2_lower_bound") as %Hi2.
    assert (is_Some (slots !! i)) as [[[dl ds] dw] Hslots_i].
    { destruct (slots !! i) as [d|]; [ by exists d | by inversion Hval_wit_i ]. }
    assert (dl = li) as Hdl_li; last subst dl.
    { rewrite Hslots_i in Hval_wit_i. by inversion Hval_wit_i. }
    (* We now reason by case on whether the enqueue at [i] was committed. *)
    destruct (was_committed (li, ds, dw)) eqn:Hcommitted.
    { (* We first consider the case where it was committed. *)
      (* If [i] has been dequeued alread: contradiction. *)
      assert (i ∉ deqs) as Hi_not_deq.
      { intros Hi_deq. specialize (Hdeqs i Hi_deq) as (H1 & H2 & H3).
        rewrite Hslots_i /= in H1. inversion H1; subst dw.
        rewrite /array_get Hslots_i in Hi. rewrite decide_True in Hi; last done.
        inversion Hi. }
      (* We clean up the prophecy. *)
      rewrite /= decide_True in Hpvs; last lia. rewrite Nat2Z.id in Hpvs.
      rewrite decide_False in Hpvs; last done.
      (* We then show that the commit prefix cannot be empty. *)
      destruct pref as [|i' new_pref].
      { exfalso. destruct cont as [i1 i2|_].
        - destruct Hinitial_cont as [-> Hi1].
          destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
          rewrite Hpvs /= in HC8. destruct HC8 as [junk HEq].
          inversion HEq as [[HEq1 HEq2]]. lia.
        - destruct cont' as [i1' i2'|bs].
          + destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
            rewrite Hpvs /= in HC8. destruct HC8 as [junk HEq].
            inversion HEq as [[HEq1 HEq2]].
            assert (back < i2'); last by lia. lia.
          + destruct Hcont as (HC1 & HC2 & HC3). rewrite Hpvs /= in HC3.
            destruct bs as [|[b_u b_ps] bs]; first by inversion HC3.
            simpl in HC3. inversion HC3 as [[HEq1 HEq2]].
            assert (block_valid slots (b_u, b_ps))
              as [Hvalid _] by apply HC1, elem_of_list_here.
            rewrite /= -HEq1 Hslots_i in Hvalid. inversion Hvalid. }
      assert (i' = i) as ->.
      { destruct cont' as [i1' i2'|bs].
        - destruct Hcont as (_ & _ & _ & _ & _ & HC).
          rewrite Hpvs in HC. destruct HC as [junk HC]. by inversion HC.
        - destruct Hcont as (_ & _ & HC).
          rewrite Hpvs in HC. by inversion HC. }
      (* We commit. *)
      pose (new_elts := map (get_value slots ({[i]} ∪ deqs)) new_pref ++ rest).
      pose (new_pvs := proph_data sz ({[i]} ∪ deqs) rs').
      iMod "AU" as (elts_AU) "[He◯ [_ Hclose]]".
      iDestruct (sync_elts with "He● He◯") as %<-.
      iMod (update_elts _ _ _ new_elts with "He● He◯") as "[He● He◯]".
      iMod ("Hclose" $! li new_elts with "[$He◯]") as "HΦ".
      { iPureIntro. rewrite /new_elts /=. by rewrite /get_value Hslots_i. }
      iModIntro. iSplitR "HΦ Hback_snap".
      { pose (new_deqs := {[i]} ∪ deqs).
        iNext. iExists back', new_pvs, new_pref, rest, cont', slots, new_deqs.
        subst new_deqs. iFrame. iSplitL "Hℓ_ar".
        { rewrite array_content_dequeue; [ done | by lia | done ]. }
        iPureIntro. repeat split_and; try done.
        - intros k. split; intros Hk; first by apply Hstate.
          intros Hk_in_deqs. apply elem_of_union in Hk_in_deqs.
          destruct Hk_in_deqs as [Hk_is_i|Hk_in_deqs].
          + apply elem_of_singleton_1 in Hk_is_i. subst k.
            rewrite /array_get Hslots_i decide_False in Hi; last done.
            rewrite /physical_value in Hi. rewrite Hslots_i in Hk.
            inversion Hk; subst dw. inversion Hi.
          + apply Hdeqs in Hk_in_deqs as (HContra & _).
            rewrite HContra in Hk. inversion Hk.
        - intros k Hk.
          assert (k ∈ i :: new_pref) as HH%Hpref by set_solver +Hk.
          destruct HH as (H1 & H2 & H3). repeat split; try done.
          apply not_elem_of_union. split; last done.
          apply not_elem_of_singleton. intros ->.
          destruct cont' as [i1' i2'|bs].
          + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & [junk HC6]).
            rewrite HC6 in Hpvs_ND.
            apply NoDup_app in Hpvs_ND as (HND & _ & _).
            apply NoDup_app in HND as (HND & _ & _).
            apply NoDup_app in HND as (HND & _ & _).
            apply NoDup_cons in HND as (HND & _). apply HND, Hk.
          + destruct Hcont as (HC1 & HC2 & HC3). rewrite HC3 in Hpvs_ND.
            apply NoDup_app in Hpvs_ND as (HND & _ & _).
            apply NoDup_app in HND as (HND & _ & _).
            apply NoDup_cons in HND as (HND & _). apply HND, Hk.
        - intros k Hk. apply elem_of_union in Hk as [Hk%elem_of_singleton_1|Hk].
          + subst k. rewrite Hslots_i /=.
            assert (dw = true) as ->.
            { rewrite /array_get Hslots_i decide_False in Hi; last done.
              rewrite /physical_value in Hi. destruct dw; first done. by inversion Hi. }
            repeat split_and; [ done | by f_equal | .. ].
            rewrite /array_get Hslots_i decide_True; [ done | by set_solver ].
          + destruct (Hdeqs k Hk) as (H1 & H2 & H3). repeat split_and; try done.
            rewrite /array_get. destruct (slots !! k) as [[[lk sk] wk]|]; last done.
            rewrite decide_True; first done. by set_solver +Hk.
        - by apply proph_data_NoDup.
        - intros k Hk. by eapply (proph_data_sz sz _ _ _ Hk).
        - destruct cont' as [i1' i2'|bs].
          + destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
            assert (i1' ≠ i) as Hi1'_not_i.
            { intros ->. assert (i ∈ i :: new_pref) as Hpref_i%Hpref by set_solver.
              by destruct Hpref_i as (_ & _ & Hpref_i). }
            repeat split_and; try done.
            * apply not_elem_of_union. split; last done. by apply not_elem_of_singleton.
            * rewrite /array_get. destruct (slots !! i1') as [di1'|]; last by inversion HC2.
              destruct di1' as [[li1' si1'] wi1']. rewrite decide_False; last by set_solver.
              inversion HC5; subst wi1'. done.
            * rewrite Hpvs /= in HC8. rewrite /new_pvs. by eapply prefix_cons_inv_2.
          + destruct Hcont as (HC1 & HC2 & HC3).
            repeat split_and; try done. rewrite Hpvs /= in HC3. by inversion HC3. }
      wp_pures. done. }
    (* If the enqueue at index [i] was not committed: contradiction. *)
    exfalso.
    assert (was_committed <$> slots !! i = Some false) as Hcom_i.
    { rewrite Hslots_i. simpl. by f_equal. }
    apply Hstate in Hcom_i. rewrite Hslots_i in Hcom_i.
    inversion Hcom_i; subst dw. rewrite /array_get Hslots_i /= in Hi.
    destruct (decide (i ∈ deqs)); by inversion Hi.
  * (* The CmpXchg failed, we continue looping. *)
    assert (array_content sz slots deqs !! i = Some NONEV) as Hcont_i.
    { rewrite array_content_lookup; last by lia. by rewrite Hi. }
    wp_apply (wp_cmpxchg_fail_offset _ _ _ _ _ _ (array_get slots deqs i) with "Hℓ_ar");
      [ by rewrite Hi | by rewrite Hi | by right | ]. iIntros "Hℓa" (rs' ->) "Hp".
    (* We can close the invariant. *)
    iModIntro. iSplitR "AU Hback_snap Hi2_lower_bound".
    { iNext. iExists _, _, _, _, cont', _, _. iFrame. iSplit; last done. iPureIntro.
      rewrite Hpvs /= decide_True; last by lia. done. }
    (* And conclude using the loop induction hypothesis. *)
    wp_pures. assert (S n - 1 = n)%Z as -> by lia. iClear "Hval_wit_i".
    iApply ("IH_loop" with "[] [] AU Hback_snap").
    - iPureIntro. lia.
    - iPureIntro. destruct cont as [i1 i2|bs]; last done.
      apply Nat.lt_eq_cases in Hcont_i1. destruct Hcont_i1 as [Hi1|Hi1]; first lia.
      exfalso. destruct Hinitial_cont as [-> Hinitial_cont].
      destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC7).
      assert (is_Some (slots !! i1)) as Hslots_i1. { apply Hslots. lia. }
      destruct Hslots_i1 as [[[li1 si1] wi1] Hslots_i1].
      rewrite /array_get Hslots_i1 decide_False in HC5; last done.
      simpl in HC5. destruct wi1; last done. clear HC5.
      rewrite array_content_lookup in Hcont_i; last by lia.
      rewrite /array_get in Hcont_i. subst i i1. rewrite Hslots_i1 in Hcont_i.
      rewrite decide_False in Hcont_i; last done. inversion Hcont_i.
    - by iFrame.
Qed.

End herlihy_wing_queue.

(** * Instantiation of the specification  ***********************************)

Definition atomic_cinc `{!heapGS Σ, !savedPropG Σ, !hwqG Σ} :
  spec.atomic_hwq Σ :=
  {| spec.new_queue_spec := new_queue_spec;
     spec.enqueue_spec := enqueue_spec;
     spec.dequeue_spec := dequeue_spec;
     spec.hwq_content_exclusive := hwq_cont_exclusive |}.

Global Typeclasses Opaque hwq_content is_hwq.
