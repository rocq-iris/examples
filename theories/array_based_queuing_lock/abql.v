(** An implementation and safety proof of the Array-Based Queuing Lock (ABQL).

    This data-structure was included in the VerifyThis 2018 program verification
    competition [1, 2]. The example is also described in the chapter "Case study:
    The Array-Based Queuing Lock" in the Iris lecture notes [2].

    1: https://hal.inria.fr/hal-01981937/document
    2: https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Verify%20This/Solutions%202018/abql.pdf
    3: https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf#section.10
 *)

From iris.program_logic Require Export weakestpre.
From stdpp Require Export list.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import numbers excl auth gset frac.
From iris.prelude Require Import options.

Section abql_code.

  (* The ABQL is a variant of a ticket lock which uses an array.

     The lock consists of three things:
     - An array of booleans which contains true at a single index and false at
       all other indices.
     - A natural number, which represents the next available ticket. Tickets are
       increasing and the remainder from dividing the ticket with the length of
       the array gives an index in the array to which the ticket corresponds.
     - The length of the array. The lock can handle at most this many
       simultaneous attempts to acquire the lock. We call this the capacity of
       the lock. *)
  Definition newlock : val :=
    λ: "cap", let: "array" := AllocN "cap" #false in
              ("array" +ₗ #0%nat) <- #true ;; ("array", ref #0, "cap").

  (* wait_loop is called by acquire with a ticket. As mentioned, the ticket
     corresponds to an index in the array. If the array contains true at that
     index we may acquire the lock otherwise we spin. *)
  Definition wait_loop : val :=
    rec: "spin" "lock" "ticket" :=
      let: "array" := Fst (Fst "lock") in (* Get the first element of the triple *)
      let: "idx" := "ticket" `rem` (Snd "lock") in (* Snd "Lock" gets the third element of the triple *)
      if: ! ("array" +ₗ "idx") then #() else ("spin" "lock" "ticket").

  (* To acquire the lock we first take the next ticket using FAA. The wait_loop
     function then spins until the ticket grants access to the lock. *)
  Definition acquire : val :=
    λ: "lock", let: "next" := Snd (Fst "lock") in
               let: "ticket" := FAA "next" #1%nat in
               wait_loop "lock" "ticket" ;;
               "ticket".

  (* To release the lock, the index in the array corresponding to the current
     ticket is set to false and the next index (possibly wrapping around the end
     of the array) is set to true. *)
  Definition release : val :=
    λ: "lock" "o", let: "array" := Fst (Fst "lock") in
                   let: "cap" := Snd "lock" in
                   "array" +ₗ ("o" `rem` "cap") <- #false ;;
                   "array" +ₗ (("o" + #1) `rem` "cap") <- #true.

End abql_code.

Module spec.

  (* Acquiring the lock consists of taking a ticket and spinning on an entry in
     the array. If there are more threads waiting to acquire the lock than there
     are entries in the array, several threads will spin on the same entry in
     the array, and they may both enter their critical section when this entry
     becomes true. Thus, to ensure safety the specification must ensure that
     this can't happen. To this end the specification is that of a ticket lock,
     but extended with _invitations_.

     Invitations are non-duplicable tokens which gives permission to acquire the
     lock. In newlock, when a lock is created with capacity `n` the same amount
     of invitations are created. These are tied to the lock through the ghost
     name γ. acquire_spec consumes one invitaiton and release_spec hands back
     one invitation. Together this ensures that at most `n` threads may
     simultaneously attempt to acquire the lock.

     invitation_split allows the client to split and combine invitations. *)

  Structure abql_spec Σ `{!heapGS Σ} := abql {
    (* Operations *)
    newlock : val;
    acquire : val;
    release : val;
    (* Predicates *)
    is_lock (γ ι κ : gname) (lock : val) (cap : nat) (R : iProp Σ) : iProp Σ;
    locked (γ κ: gname) (o : nat) : iProp Σ;
    invitation (ι : gname) (n : nat) (cap : nat) : iProp Σ;
    (* General properties of the predicates *)
    is_lock_persistent γ ι κ lock cap R : Persistent (is_lock γ ι κ lock cap R);
    locked_timeless γ κ o : Timeless (locked γ κ o);
    locked_exclusive γ κ o o' : locked γ κ o -∗ locked γ κ o' -∗ False;
    invitation_split γ (n m cap : nat) :
      invitation γ (n + m) cap ⊣⊢ invitation γ n cap ∗ invitation γ m cap;
    (* Program specs *)
    newlock_spec (R : iProp Σ) (cap : nat) :
      {{{ R ∗ ⌜0 < cap⌝ }}}
        newlock (#cap)
      {{{ lk γ ι κ, RET lk; (is_lock γ ι κ lk cap R) ∗ invitation ι cap cap }}};
    acquire_spec γ ι κ lk cap R :
      {{{ is_lock γ ι κ lk cap R ∗ invitation ι 1 cap}}}
        acquire lk
      {{{ t, RET #t; locked γ κ t ∗ R }}};
    release_spec γ ι κ lk cap o R :
      {{{ is_lock γ ι κ lk cap R ∗ locked γ κ o ∗ R }}}
        release lk #o
      {{{ RET #(); invitation ι 1 cap }}};
  }.

End spec.

Section algebra.

  (* We create a resource algebra used to represent invitations. The RA can be
     thought of as "addition with an upper bound". The carrier of the resource
     algebra is pairs of natural numbers. The first number represents how many
     invitations we have and the second how many invitations exists in total.

     We want (a, n) ⋅ (b, n) to be equal to (a + b, n). We never combine
     elements (a, n) ⋅ (b, m) where n ≠ m. Hence what happens it that case is
     arbitary, as long the laws for a RA are satisfied. We can not, for instance,
     just disregard the second upper bound as that whould violate commutativity,
     and using `max` would not satisfy the laws for validity. We could use
     agreement, but choose to use `min` instead as it is easier to work with. *)
  Record addb : Type := Addb { addb_proj : nat * min_nat }.

  Canonical Structure sumRAC := leibnizO addb.

  Local Instance addb_op : Op addb := λ a b, Addb (addb_proj a ⋅ addb_proj b).

  (* The definition of validity matches the intuition that if there exists n
     invitations in totoal then one can at most have n invitations. *)
  Local Instance addb_valid : Valid addb :=
    λ a, match a with Addb (x, MinNat n) => x ≤ n end.

  (* Invitations should not be duplicable. *)
  Local Instance addb_pcore : PCore addb := λ _, None.

  (* We need these auxiliary lemmas in the proof below. *)
  Lemma sumRA_op_second a b (n : min_nat) : Addb (a, n) ⋅ Addb (b, n) = Addb (a + b, n).
  Proof. by rewrite /op /addb_op -pair_op idemp_L. Qed.

  (* If (a, n) is valid ghost state then we can conclude that a ≤ n *)
  Lemma sumRA_valid a n : ✓(Addb (a, n)) ↔ a ≤ min_nat_car n.
  Proof. destruct n. split; auto. Qed.

  Definition sumRA_mixin : RAMixin addb.
  Proof.
    split; try apply _; try done.
    - intros ???. rewrite /op /addb_op /=. apply f_equal, assoc, _.
    - intros ??. rewrite /op /addb_op /=. apply f_equal, comm, _.
    - intros [[?[?]]] [[?[?]]]. rewrite 2!sumRA_valid nat_op /=. lia.
  Qed.

  Canonical Structure sumRA := discreteR addb sumRA_mixin.

  Global Instance sumRA_cmra_discrete : CmraDiscrete sumRA.
  Proof. apply discrete_cmra_discrete. Qed.

  Class sumG Σ := SumG { sum_inG :> inG Σ sumRA }.
  Definition sumΣ : gFunctors := #[GFunctor sumRA].

  Global Instance subG_sumΣ {Σ} : subG sumΣ Σ → sumG Σ.
  Proof. solve_inG. Qed.

End algebra.

Section array_model.

  (* A few auxillary lemmas used to handle arrays in relation to the ABQL. *)

  Context `{!heapGS Σ}.

  (* is_array relates a location to a list of booleans. We use this since "_ ↦∗
     _" relates a location to a list of values, but we need the extra
     information offered here. *)
  Definition is_array (array : loc) (xs : list bool) : iProp Σ :=
    let vs := (fun b => # (LitBool b)) <$> xs
    in array ↦∗ vs.

  (* `list_with_one n i` denotes a list with lenght n, a single true at index i,
     and false everywhere else. *)
  Definition list_with_one (length index : nat) : list bool :=
    <[index:=true]> (replicate length false).

  Lemma array_store E (i : nat) (v : bool) arr (xs : list bool) :
    {{{ ⌜i < length xs⌝ ∗ ▷ is_array arr xs }}}
      #(arr +ₗ i) <- #v
    @ E {{{ RET #(); is_array arr (<[i:=v]>xs) }}}.
  Proof.
    iIntros (ϕ) "[% isArr] Post".
    unfold is_array.
    iApply (wp_store_offset with "isArr").
    { apply lookup_lt_is_Some_2. by rewrite fmap_length. }
    rewrite (list_fmap_insert ((λ b : bool, #b) : bool → val) xs i v).
    iAssumption.
  Qed.

  Lemma insert_list_with_one (i : nat) l :
    <[i:=false]> (list_with_one l i) = replicate l false.
  Proof.
    by rewrite /list_with_one list_insert_insert insert_replicate.
  Qed.

  (* The repeat code behaves similar to the replicate function *)
  Lemma array_repeat (b : bool) (n : nat) :
    {{{ ⌜0 < n⌝ }}} AllocN #n #b {{{ arr, RET #arr; is_array arr (replicate n b) }}}.
  Proof.
    iIntros (ϕ ?%inj_lt) "Post".
    iApply wp_allocN; try done.
    iNext. iIntros (l) "[lPts _]".
    iApply "Post".
    unfold is_array.
    rewrite Nat2Z.id.
    rewrite -> fmap_replicate.
    iAssumption.
  Qed.

End array_model.

(** The CMRAs we need. *)
Class alockG Σ := {
  tlock_G :> inG Σ (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat)));
  tlock_sumG :> sumG Σ;
  tlock_tokenG :> inG Σ ((prodR (optionUR (exclR unitO)) (optionUR (exclR unitO))));
}.

Section proof.

  Context `{!heapGS Σ, !alockG Σ}.
  Let N := nroot .@ "abql".

  (* The ghost state both, left, and right is used to keep track of the state of
     the lock:
     State of lock:  open --> closed --> clopen --> open
     Owned by lock:  both --> left   --> right  --> both
     Outside lock:   none --> right  --> left   --> none *)
  Definition both (κ : gname) : iProp Σ := own κ (Excl' (), Excl' ()).
  Definition left (κ : gname) : iProp Σ := own κ (Excl' (), None).
  Definition right (κ : gname) : iProp Σ := own κ (None, Excl' ()).

  Definition invitation (ι : gname) (x cap : nat) : iProp Σ :=
    own ι (Addb (x, MinNat cap))%I.

  Definition issued (γ : gname) (x : nat) : iProp Σ := own γ (◯ (ε, GSet {[ x ]}))%I.

  (* The lock invariant *)
  Definition lock_inv (γ ι κ : gname) (arr : loc) (cap : nat) (nextPtr : loc) (R : iProp Σ) : iProp Σ :=
    (∃ (o i : nat) (xs : list bool), (* o: who may acquire the lock, i: nr of invitations in lock *)
        ⌜length xs = cap⌝ ∗
        nextPtr ↦ #(o + i)%nat ∗
        is_array arr xs ∗
        invitation ι i cap ∗ (* The invitations currently owned by the lock. *)
        own γ (● (Excl' o, GSet (set_seq o i))) ∗
        ((* Lock is open, R belongs to the lock *)
         (own γ (◯ (Excl' o, GSet ∅)) ∗ R ∗ both κ ∗ ⌜xs = list_with_one cap (Nat.modulo o cap)⌝) ∨
         (* Lock is clopen, in the process of being released. *)
         (issued γ o ∗ right κ ∗ ⌜xs = replicate cap false⌝) ∨
         (* Lock is closed, i.e. it is locked *)
         (issued γ o ∗ left κ ∗ ⌜xs = list_with_one cap (Nat.modulo o cap)⌝)))%I.

  (* The lock predicate *)
  (* cap is the length or the capacity of the lock *)
  Definition is_lock γ ι κ (lock : val) (cap : nat) P :=
    (∃ (arr : loc) (nextPtr : loc),
        ⌜lock = (#arr, #nextPtr, #cap)%V⌝ ∗
        ⌜0 < cap⌝ ∗
        inv N (lock_inv γ ι κ arr cap nextPtr P))%I.

  Definition locked (γ κ : gname) (o : nat) : iProp Σ := (own γ (◯ (Excl' o, GSet ∅)) ∗ right κ)%I.

  Global Instance is_lock_persistent γ ι κ lk n R : Persistent (is_lock γ ι κ lk n R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ κ o : Timeless (locked γ κ o).
  Proof. apply _. Qed.

  Lemma locked_exclusive (γ κ : gname) o o' : locked γ κ o -∗ locked γ κ o' -∗ False.
  Proof.
    iIntros "[H1 _] [H2 _]".
    iDestruct (own_valid_2 with "H1 H2") as %[[] _]%auth_frag_op_valid_1.
  Qed.

  (* Only one thread can know the exact value of `o`. *)
  Lemma know_o_exclusive γ o o' :
    own γ (◯ (Excl' o, GSet ∅)) -∗ own γ (◯ (Excl' o', GSet ∅)) -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[[]]%auth_frag_op_valid_1.
  Qed.

  (* Lemmas about both, left, and right. *)
  Lemma left_left_false (κ : gname) : left κ -∗ left κ -∗ False.
  Proof.
    iIntros "L L'". iCombine "L L'" as "L".
    iDestruct (own_valid with "L") as %[Hv _]. inversion Hv.
  Qed.

  Lemma right_right_false (κ : gname) : right κ -∗ right κ -∗ False.
  Proof.
    iIntros "R R'". iCombine "R R'" as "R".
    iDestruct (own_valid with "R") as %[_ Hv]. inversion Hv.
  Qed.

  Lemma both_split (κ : gname) : both κ -∗ (left κ ∗ right κ).
  Proof. iIntros "Both". iApply own_op. iFrame. Qed.

  Lemma left_right_to_both (κ : gname) : left κ -∗ right κ -∗ both κ.
  Proof. iIntros "L R". iCombine "L" "R" as "?". iFrame. Qed.

  Lemma valid_ticket_range (γ : gname) (x o i : nat) :
    own γ (◯ (ε, GSet {[ x ]})) -∗ own γ (● (Excl' o, GSet (set_seq o i)))
        -∗ ⌜o ≤ x < o + i⌝ ∗ own γ (◯ (ε, GSet {[ x ]})) ∗ own γ (● (Excl' o, GSet (set_seq o i))).
  Proof.
    iIntros "P O".
    iDestruct (own_valid_2 with "O P") as %[[_ xIncl%gset_disj_included]%prod_included Hv]%auth_both_valid_discrete.
    iFrame. iPureIntro.
    apply elem_of_subseteq_singleton, elem_of_set_seq in xIncl.
    lia.
  Qed.

  Lemma ticket_i_gt_zero (γ : gname) (o i : nat) :
    own γ (◯ (ε, GSet {[ o ]})) -∗ own γ (● (Excl' o, GSet (set_seq o i)))
      -∗ ⌜0 < i⌝ ∗ own γ (◯ (ε, GSet {[ o ]})) ∗ own γ (● (Excl' o, GSet (set_seq o i))).
  Proof.
    iIntros "P O".
    iDestruct (own_valid_2 with "O P") as %HV%auth_both_valid_discrete.
    iFrame. iPureIntro.
    destruct HV as [[_ H%gset_disj_included]%prod_included _].
    apply elem_of_subseteq_singleton, set_seq_len_pos in H.
    lia.
  Qed.

  Lemma invitation_cap_bound γ i cap :
    invitation γ i cap -∗ ⌜i ≤ cap⌝.
  Proof.
    iIntros "I". by iDestruct (own_valid with "I") as %H.
  Qed.

  Lemma invitation_split γ (n m cap : nat) :
    invitation γ (n + m) cap  ⊣⊢ invitation γ n cap ∗ invitation γ m cap.
  Proof.
    iSplit.
    - iIntros "I". iDestruct (own_valid with "I") as %Hv.
      by rewrite -own_op sumRA_op_second.
    - iIntros "[I1 I2]". iCombine "I1 I2" as "I". by rewrite sumRA_op_second.
  Qed.

  Lemma invitation_split_one γ (i cap : nat) :
    0 < i → invitation γ i cap -∗ invitation γ (i - 1) cap ∗ invitation γ 1 cap.
  Proof.
    iIntros (Hl) "I". iDestruct (own_valid with "I") as %Hv.
    rewrite -own_op sumRA_op_second Nat.sub_add; auto; lia.
  Qed.

  Lemma newlock_spec (R : iProp Σ) (cap : nat) :
    {{{ R ∗ ⌜0 < cap⌝ }}}
      newlock (#cap)
    {{{ lk γ ι κ, RET lk; (is_lock γ ι κ lk cap R) ∗ invitation ι cap cap }}}.
  Proof.
    iIntros (Φ) "[Pre %] Post".
    wp_lam.
    wp_apply array_repeat; first done.
    iIntros (arr) "isArr".
    wp_pures.
    wp_apply (array_store with "[$isArr]"); first by rewrite replicate_length.
    iIntros "isArr".
    (* We allocate the ghost states for the tickets and value of o. *)
    iMod (own_alloc (● (Excl' 0, GSet ∅) ⋅ ◯ (Excl' 0, GSet ∅))) as (γ) "[Hγ Hγ']".
    { by apply auth_both_valid_discrete. }
    (* We allocate the ghost state for the invitations. *)
    iMod (own_alloc (Addb (cap, MinNat cap) ⋅ Addb (0, MinNat cap))) as (ι) "[Hinvites HNoInvites]".
    { rewrite sumRA_op_second Nat.add_0_r. apply sumRA_valid. auto. }
    (* We allocate the ghost state for the lock state indicatior. *)
    iMod (own_alloc ((Excl' (), Excl' ()))) as (κ) "Both". { done. }
    wp_alloc p as "pts".
    iMod (inv_alloc _ _ (lock_inv γ ι κ arr cap p R) with "[-Post Hinvites]").
    { iNext. rewrite /lock_inv. iExists 0, 0, (<[0:=true]> (replicate cap false)).
      iFrame. iSplitR.
      - by rewrite insert_length replicate_length.
      - iLeft. iFrame. rewrite Nat.mod_0_l //. lia. }
    wp_pures.
    iApply "Post".
    rewrite /is_lock. iFrame.
    iExists _, _. auto.
  Qed.

  Lemma rem_mod_eq (x y : nat) : (0 < y) → (x `rem` y)%Z = x `mod` y.
  Proof.
    intros Hpos. rewrite Z.rem_mod_nonneg; [rewrite Nat2Z.inj_mod| |]; lia.
  Qed.

  Lemma minus_plus_eq a b c : (a - b)%Z = c → a = (c + b)%Z.
  Proof. lia. Qed.

  Lemma mod_fact_Z (t o i cap : Z) :
    (0 < cap → o <= t < o + i → i <= cap → t `mod` cap = o `mod` cap → t = o)%Z.
  Proof.
    intros LeqCap [sLeX xLeSCap] ILeqCap ModEq.
    assert (t < o + cap)%Z as Eq1; first lia.
    rewrite (Z.div_mod o cap) in sLeX Eq1 |- *; last lia.
    rewrite (Z.div_mod t cap) in sLeX Eq1 |- *; last lia.
    remember (t `mod` cap)%Z as a. remember (o `mod` cap)%Z as b.
    remember (o `div` cap)%Z as c. remember (t `div` cap)%Z as d.
    rewrite -> ModEq in * |- *.
    assert (c ≤ d)%Z. { eapply Zmult_lt_0_le_reg_r; first by apply LeqCap. subst. lia. }
    assert (d < 1 + c)%Z. { eapply Zmult_lt_reg_r; first by apply LeqCap. lia. }
    assert (d = c) as ->; first lia.
    reflexivity.
  Qed.

  Lemma mod_fact (t o i cap : nat) :
    0 < cap → o <= t → t < o + i → i <= cap → t `mod` cap = o `mod` cap → t = o.
  Proof.
    intros LeqCap SLeqX XLeqSi ILeqCap ModEq%inj_eq.
    repeat rewrite Nat2Z.inj_mod in ModEq; try lia.
    apply Nat2Z.inj.
    eapply (mod_fact_Z _ _ i cap); lia.
  Qed.

  Lemma nth_list_with_one (n a b : nat) :
    list_with_one n a !! b = Some true → a = b.
  Proof.
    rewrite /list_with_one.
    by intros [[Eq] | [_ [[=] _]%lookup_replicate_1]]%list_lookup_insert_Some.
  Qed.

  Lemma wait_loop_spec γ ι κ lk cap t R :
    {{{ is_lock γ ι κ lk cap R ∗ issued γ t }}}
      wait_loop lk #t
    {{{ RET #(); locked γ κ t ∗ R }}}.
  Proof.
    iIntros (ϕ) "(Lock & Ticket) Post".
    (* Since `wait_loop` invokes itself recursively we use Löb *)
    iLöb as "IH".
    wp_lam. wp_let.
    iDestruct "Lock" as (arr nextPtr -> capPos) "#LockInv".
    wp_pures.
    wp_bind (! _)%E.
    iInv N as (o i xs) "(>%lenEq & >nextPts & isArr & >Inv & Auth & Part)" "Close".
    rewrite /is_array rem_mod_eq //.
    pose proof (lookup_lt_is_Some_2 ((λ b : bool, #b) <$> xs) ((t `mod` cap))) as [x1 Hsome].
    { subst. rewrite fmap_length. apply Nat.mod_upper_bound. lia. }
    wp_apply (wp_load_offset with "isArr"); first apply Hsome.
    iIntros "isArr".
    apply list_lookup_fmap_inv in Hsome as (x & -> & xsLookup).
    destruct x.
    - rewrite /issued.
      iDestruct (valid_ticket_range with "Ticket Auth") as "([% %] & Ticket & Auth)".
      iDestruct (invitation_cap_bound with "Inv") as "%".
      (* We now destruct the three cases that the lock can be in. *)
      iDestruct "Part" as "[(Ho & Hr & Both & %xsEq) | [(Ticket2 & Right & %xsEq) | (Ticket2 & Left & %xsEq)]]".
      * (* The case where the lock is currently open. *)
        rewrite xsEq in xsLookup.
        apply nth_list_with_one in xsLookup.
        assert (t = o) as ->. { apply (mod_fact _ _ i cap); done. }
        iDestruct (both_split with "Both") as "[Left Right]".
        iMod ("Close" with "[nextPts isArr Inv Auth Ticket Left]") as "_".
        { iNext. iExists o, i, (list_with_one cap (o `mod` cap)).
          rewrite /is_array xsEq. iFrame.
          iSplit.
          - by rewrite /list_with_one insert_length replicate_length.
          - iRight. iRight. iFrame. done. }
        iModIntro. wp_pures. iApply "Post". by iFrame.
      * (* The case where the lock is in the clopen state. In this state all the
           indices in the array are false and hence we can not possibly have
           read a true in the array. *)
        rewrite xsEq in xsLookup.
        apply lookup_replicate_1 in xsLookup as [[=] _].
      * (* The case where the lock is closed. *)
        rewrite xsEq in xsLookup. apply nth_list_with_one in xsLookup.
        assert (t = o) as ->. { apply (mod_fact _ _ i (cap)); auto. }
        iDestruct (own_valid_2 with "Ticket Ticket2")
          as % [_ ?%gset_disj_valid_op]%auth_frag_op_valid_1.
        set_solver.
    - iMod ("Close" with "[nextPts isArr Inv Auth Part]") as "_".
      { iNext. iExists o, i, xs. iFrame. auto. }
      iModIntro. wp_pures. iApply ("IH" with "[LockInv] Ticket").
      { iExists arr, nextPtr. auto. }
      done.
  Qed.

  Lemma acquire_spec γ ι κ lk cap R :
    {{{ is_lock γ ι κ lk cap R ∗ invitation ι 1 cap}}}
      acquire lk
    {{{ t, RET #t; locked γ κ t ∗ R }}}.
  Proof.
    iIntros (ϕ) "[#IsLock Invitation] Post".
    iPoseProof "IsLock" as (arr nextPtr) "(-> & % & LockInv)".
    wp_lam. wp_pures. wp_bind (FAA _ _).
    iInv N as (o i xs) "(>% & >nextPts & psPts & >Invs & >Auth & np)" "Close".
    wp_faa.
    iMod (own_update with "Auth") as "[Auth Hofull]".
    { eapply auth_update_alloc, prod_local_update_2.
      eapply (gset_disj_alloc_empty_local_update _ {[ (o + i) ]}).
      apply (set_seq_S_end_disjoint o). }
    iMod ("Close" with "[-Post Hofull]") as "_".
    { iNext. rewrite /lock_inv. iExists o, (i+1), xs. iFrame.
      iSplit; first done.
      iSplitL "nextPts".
      { repeat rewrite Nat2Z.inj_add. by rewrite Z.add_assoc. }
      iSplitL "Invitation Invs".
      { rewrite /invitation -sumRA_op_second own_op. iFrame. }
      by rewrite -(set_seq_S_end_union_L) Nat.add_1_r. }
    iModIntro.
    wp_let.
    wp_apply (wait_loop_spec γ ι κ (#arr, #nextPtr, #cap)%V cap (o + i) R with "[Hofull]").
    { rewrite /issued. by iFrame. }
    iIntros "[locked Res]". wp_seq. iApply "Post". by iFrame.
  Qed.

  Lemma frame_update_lemma_discard_ticket o i :
    ● (Excl' o, GSet (set_seq o i)) ⋅ (◯ (Excl' o, GSet ∅) ⋅ ◯ (ε, GSet {[o]})) ~~>
    ● (Excl' (o + 1), GSet (set_seq (o + 1) (i - 1))) ⋅ (◯ (Excl' (o + 1), GSet ∅)).
  Proof.
    rewrite -auth_frag_op -pair_op right_id left_id.
    apply auth_update.
    destruct i.
    - apply local_update_total_valid.
      intros _ _ [_ H%gset_disj_included]%prod_included.
      set_solver.
    - apply prod_local_update; simpl.
      + apply option_local_update, exclusive_local_update. done.
      + rewrite Nat.sub_0_r Nat.add_1_r -gset_op -gset_disj_union.
        * apply gset_disj_dealloc_empty_local_update.
        * apply set_seq_S_start_disjoint.
  Qed.

  Lemma release_spec γ ι κ lk cap o R :
    {{{ is_lock γ ι κ lk cap R ∗ locked γ κ o ∗ R }}}
      release lk #o
    {{{ RET #(); invitation ι 1 cap }}}.
  Proof.
    iIntros (ϕ) "(#IsLock & [Locked Right] & R) Post".
    iPoseProof "IsLock" as (arr nextPtr) "(-> & % & LockInv)".
    wp_lam. wp_pures.
    (* Focus the store such that we can open the invariant. *)
    wp_bind (_ <- _)%E.
    iInv N as (o' i xs) "(>%lenEq & >nextPts & arrPts & >Invs & >Auth & Part)" "Close".
    (* We want to show that o and o' are equal. We know this from the loked γ o ghost state. *)
    iDestruct (own_valid_2 with "Auth Locked") as
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid_discrete.
    rewrite rem_mod_eq //.
    iApply (array_store with "[arrPts]").
    { iFrame. iPureIntro. rewrite lenEq. apply Nat.mod_upper_bound. lia. }
    iModIntro. iIntros "psPts".
    iDestruct "Part" as "[(Locked' & _ & Both & _) | [(_ & Right' & _) | (Issued & Left & %xsEq)]]".
    { iDestruct (know_o_exclusive with "Locked Locked'") as %[]. }
    { iDestruct (right_right_false with "Right Right'") as %[]. }
    iMod ("Close" with "[nextPts Invs Auth psPts Issued Right]") as "_".
    { iNext. iExists o, i, (<[(o `mod` cap) := false]> xs).
      rewrite insert_length.
      iFrame. iSplit; first done.
      iRight. iLeft. iFrame. iPureIntro. subst.
      rewrite -> xsEq at 2.
      by rewrite insert_list_with_one. }
    clear xsEq lenEq xs i.
    iModIntro. wp_pures.
    rewrite -(Nat2Z.inj_add o 1).
    iInv N as (o' i xs) "(>%Hlen & >nextPts & arrPts & >Invs & >Auth & Part)" "Close".
    (* We destruct the disjunction in the lock invariant. We know that we are in
       the half-locked state so the first and third case results in
       contradictions. *)
    iDestruct "Part" as "[(>Locked' & _ & Both & _) | [(Issued & Right & >%xsEq) | (Issued & >Left' & Eq)]]".
    * iDestruct (know_o_exclusive with "Locked Locked'") as "[]".
    (* This is the case where the lock is clopen, that is, the actual state
       of the lock. *)
    * iDestruct (own_valid_2 with "Auth Locked") as
          %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid_discrete.
      rewrite rem_mod_eq //.
      iApply (wp_store_offset with "arrPts").
      { apply lookup_lt_is_Some_2. rewrite fmap_length Hlen. apply Nat.mod_upper_bound. lia. }
      iModIntro. iIntros "isArr".
      (* Combine the left and right we have into a both. *)
      iDestruct (left_right_to_both with "Left Right") as "Both".
      iDestruct (ticket_i_gt_zero with "Issued Auth") as "(% & Issued & Auth)".
      iMod (own_update with "[Issued Auth Locked]") as "Hγ".
      { apply frame_update_lemma_discard_ticket. }
      { rewrite own_op own_op. iFrame. }
      iDestruct "Hγ" as "[Locked Auth]".
      iDestruct (invitation_split_one with "Invs") as "[Invs Inv]"; first done.
      iMod ("Close" with "[nextPts Invs Auth isArr Both R Locked]") as "_".
      { iNext. iExists (o + 1), (i - 1), (list_with_one cap ((o + 1) `mod` cap)).
        assert (o + 1 + (i - 1) = o + i) as -> by lia.
        iFrame.
        iSplit. { by rewrite /list_with_one insert_length replicate_length. }
        iSplitL "isArr". { by rewrite /list_with_one /is_array list_fmap_insert xsEq. }
        iLeft. iFrame. done. }
      iModIntro. iApply "Post". done.
    * iDestruct (left_left_false with "Left Left'") as "[]".
  Qed.

End proof.

Program Definition abql `{!heapGS Σ, !alockG Σ} : spec.abql_spec Σ :=
  {| spec.newlock := newlock;
     spec.acquire := acquire;
     spec.release := release;
     spec.is_lock := is_lock;
     spec.locked := locked;
     spec.invitation := invitation;
     spec.is_lock_persistent := is_lock_persistent;
     spec.locked_timeless := locked_timeless;
     spec.locked_exclusive := locked_exclusive;
     spec.invitation_split := invitation_split;
     spec.newlock_spec := newlock_spec;
     spec.acquire_spec := acquire_spec;
     spec.release_spec := release_spec;
  |}.
