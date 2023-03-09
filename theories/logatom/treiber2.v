(****************************************************************************)
(*      Logically atomic specification of the Treiber stack algorithm       *)
(*                                                                          *)
(*         by Rodolphe Lepigre (with a lot of help from Ralf Jung)          *)
(*          see https://gitlab.mpi-sws.org/lepigre/treiber_stack            *)
(****************************************************************************)

From iris.algebra Require Import excl auth list.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.


(** * Definition of the functions *******************************************)

(** A stack is (physically) represented as a pointer to a linked list. When we
    create a new stack, it initially points to an empty list. And there is, of
    course, no potential race condition here since only the current thread can
    now the value of the freshly allocated pointer. *)
Definition new_stack : val :=
  λ: <>, ref NONEV.

(** To push an element on a stack we remember the old head of the pointed list
    list, create a new cell containing both the element and the old head,  and
    then we perform a CAS (Compare And Set). We thus (atomically) test whether
    the stack still points to the old head, and if that is indeed the case, we
    simultaneously set the stack to point to the newly created cell. Note that
    if the CAS was successful, then the element has been added to the list. If
    it failed, we start over from scratch with a recursive call. *)
Definition push_stack : val :=
  rec: "push" "elt" "stack" :=
    let: "old_head" := !"stack" in
    let: "cell" := ("elt", "old_head") in
    if: CAS "stack" "old_head" (SOME (ref "cell")) then #()
    else "push" "elt" "stack".

(** To pop an element from the stack, we first remember the head of the linked
    list, and then we match on its value. If it is the end of the list (NONE),
    then the function returns NONE. If the list is non-empty, we load the cell
    containing both: the head element and the pointer to the tail of the list.
    We then perform a CAS: if the stack still points to the (previous) head of
    the list, then we set it to point to the tail. If the CAS is successful we
    return the element (wrapped in a SOME). Otherwise we start over. Note that
    in the case where the pointed list is empty the linearization point occurs
    on the first access to the stack. Otherwise it occurs at the CAS. *)
Definition pop_stack : val :=
  rec: "pop" "stack" :=
    let: "old_top" := !"stack" in
    match: "old_top" with
      NONE     => NONE
    | SOME "p" =>
       let: "cell" := !"p" in
       if: CAS "stack" "old_top" (Snd "cell") then SOME (Fst "cell")
       else "pop" "stack"
    end.


(** * Definition of the required camera *************************************)

Class stackG Σ := StackG {
  stack_tokG :> inG Σ (authR (optionUR (exclR (listO valO)))) }.

Definition stackΣ : gFunctors :=
  #[GFunctor (authR (optionUR (exclR (listO valO))))].

Global Instance subG_stackΣ {Σ} : subG stackΣ Σ → stackG Σ.
Proof. solve_inG. Qed.

(* Put some things in the context. *)
Section treiber_stack.
Context `{!heapGS Σ, !stackG Σ}.
Context (N : namespace).
Notation iProp := (iProp Σ).


(** * Representation relations and invariant used in the specification ******)

(** Utility function injecting (optional) locations into values. *)
Definition to_val (lopt : option loc) : val :=
  match lopt with
  | None   => NONEV
  | Some ℓ => SOMEV #ℓ
  end%I.

(** Representation relation for lists: the (optional) location [lopt] (in fact
    [to_val lopt]) physically represents the (Coq) list [xs]. *)
Fixpoint phys_list (lopt : option loc) (xs : list val) : iProp :=
  match (lopt, xs) with
  | (None  , []     ) => True
  | (None  , _ :: _ ) => False
  | (Some _, []     ) => False
  | (Some ℓ, x :: xs) => ∃ r, ℓ ↦□ (x, to_val r) ∗ phys_list r xs
  end%I.

(** Representation relation for stacks: the location [ℓ] physically represents
    a stack whose elements are those of [xs]. More precisely, [ℓ] is a pointer
    to a linked list, representing [xs]. *)
Definition phys_stack (ℓ : loc) (xs : list val) : iProp :=
  (∃ r, ℓ ↦ to_val r ∗ phys_list r xs)%I.

(** Statement of the invariant maintained for a stack pointed to by (location)
    [ℓ], and uniquely identified by the global name [γ]. Intuitively, there is
    a coq list [xs] such that [ℓ] physically represents [xs], and the value of
    [xs] is stored in ghost state whose authoritative  part  is  (exclusively)
    owned by the invariants.  This always keeps the ghost state in  sync  with
    the physical state, meaning that the ownership of a fragment [own γ (◯ _)]
    actually becomes meaningful to make statements about the list because both
    are tied together by this invariant. *)
Definition stack_inv (ℓ : loc) (γ : gname) : iProp :=
  (∃ xs, phys_stack ℓ xs ∗ own γ (● (Some ((Excl xs)))))%I.

(** Invariant assertion for a stack pointed to by [ℓ], and uniquely identified
    by the global name [γ].  Note that the namespace [N] is quantified over in
    the whole section. It can thus be instantiated to fit any particular need,
    when using this module as a library. *)
Definition is_stack (ℓ : loc) (γ : gname) : iProp :=
  inv N (stack_inv ℓ γ).

(** Local view of the contents [xs] of the stack that is (uniquely) identified
    by the global name [γ]. Note that this proposition is independent from the
    particular location at which the stack is stored,  which can only be owned
    by one particular thread at a time. *)
Definition stack_cont (γ : gname) (xs : list val) : iProp :=
  (own γ (◯ (Some ((Excl xs)))))%I.


(** * Useful lemmas and typeclass instances *********************************)

(** Injectivity of [to_val]. *)
Local Instance to_val_inj : Inj (=) (=) to_val.
Proof.
  intros l1 l2 H. case l1, l2; try done. inversion H. reflexivity.
Qed.

(** Persistence of the [phys_list] relation. *)
Global Instance phys_list_dup l xs : Persistent (phys_list l xs).
Proof. revert l. induction xs; apply _. Qed.

(** Timelessness of the [phys_list] relation. *)
Global Instance phys_list_timeless l xs : Timeless (phys_list l xs).
Proof.
  revert l. induction xs; apply _.
Qed.

(** The following two lemmas have been borrowed from the POPL 18 Iris tutorial
    (see https://gitlab.mpi-sws.org/iris/tutorial-popl18). *)

(** The view of the authority agrees with the local view. *)
Lemma auth_agree γ xs ys :
  own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
Proof.
  iIntros "Hγ● Hγ◯". by iCombine "Hγ● Hγ◯"
    gives %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
Qed.

(** The view of the authority can be updated together with the local view. *)
Lemma auth_update γ ys xs1 xs2 :
  own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
    own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
    with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.


(** * Automation hints for [eauto] ******************************************)

(** The following hints allow [eauto] to work with the above definitions. When
    a simple goal involving only framing and the instantiation of existentials
    is encoutered, we can usually conclude with [eauto with iFrame]. The hints
    are mainly useful for unfolding definitions and instantiating existentials
    with a reasonable choice of head constructor. *)

Local Hint Extern 0 (environments.envs_entails _
  (phys_stack _ [])) => iExists None : core.

Local Hint Extern 0 (environments.envs_entails _
  (phys_stack _ (_ :: _))) => iExists (Some _) : core.

Local Hint Extern 10 (environments.envs_entails _
  (phys_stack _ _)) => unfold phys_stack : core.

Local Hint Extern 0 (environments.envs_entails _
  (stack_inv _ _)) => unfold stack_inv : core.

Local Hint Extern 0 (environments.envs_entails _
  (phys_list None [])) => simpl : core.

Local Hint Extern 0 (environments.envs_entails _
  (phys_list (Some _) (_ :: _))) => simpl : core.


(** * Specification *********************************************************)

(** The specification of [new_stack] is straightforward: with no precondition,
    the creation of a new stack yields a location that is pointing to a stack,
    and it is initially empty. The only interesting thing to note here is that
    an existential quantifier is used in the postcondition to obtain a (fresh)
    name [γ] for the created stack. This ensures that different stacks will be
    given different names. *)
Lemma new_stack_spec :
  {{{ True }}}
    new_stack #()
  {{{ ℓ γ, RET #ℓ; is_stack ℓ γ ∗ stack_cont γ [] }}}.
Proof.
  (* Introduce things into the Coq and Iris contexts. Throw away the [True]
     precondition. *)
  iIntros (Φ) "_ HΦ".
  (* We step through the program: β-reduce and allocate a location [ℓ]. *)
  wp_lam. wp_alloc ℓ as "Hl". (* We have full ownership of [ℓ] in [Hl]. *)
  (* We now need to establish the invariant. First, we allocate an instance of
     our camera named [γ], containing the empty list. This step (and the next)
     requires the fancy update modality that was introduced earlier. *)
  iMod (own_alloc (● (Some (Excl [])) ⋅ ◯ (Some (Excl []))))
    as (γ) "[Hγ● Hγ◯]";
    (* Validity is trivial. *) first by apply auth_both_valid_discrete.
  (* We can then allocate the invariant (with mask [N]).  Note that we can use
     [eauto 10 with iFrame] to prove [▷ stack_inv ℓ γ]. *) 
  iMod (inv_alloc N _ (stack_inv ℓ γ) with "[Hl Hγ●]")
    as "#Inv"; first eauto 10 with iFrame.
  (* We can now eliminate the modality and establish the postcondition. *)
  iModIntro. iApply "HΦ". eauto with iFrame.
Qed.

(** The specification of [push_stack] depends on a location [ℓ] and a name [γ]
    assumed to correspond to a stack (created using [new_stack]),  and a value
    [v] that is being pushed. A logically atomic Hoare triple is used in order
    to ensure linearizability (i.e., the existence of a linearization point in
    the execution of the push operation). As a consequence the precondition of
    the triple can only be accessed during a physically atomic operation,  and
    the knowledge gained must then either be forgotten (abort operation) or it
    should lead to a one shot update (commit operation) during the same atomic
    operation where the precondition was accessed. In this second case we lose
    the possibility of accessing the precondition again, unlike with abort. *)
Lemma push_stack_spec (ℓ : loc) (γ : gname) (v : val) :
  is_stack ℓ γ -∗
  <<< ∀∀ (xs : list val), stack_cont γ xs >>>
    push_stack v #ℓ @ ↑N
  <<< stack_cont γ (v :: xs) , RET #() >>>.
Proof.
  (* Introduce things into the Coq and Iris contexts, and use induction. *)
  iIntros "#HInv" (Φ) "AU". iLöb as "IH".
  (* Evaluate the first steps of the program, and focus on the load. *)
  wp_lam. wp_let. wp_bind (! _)%E.
  (* Since an atomic operation is in focus we can access the invariant. Hence,
     we will be able to learn that [ℓ] actually points to something. *)
  iInv "HInv" as (xs) ">[HPhys Hγ●]".
  unfold phys_stack. iDestruct "HPhys" as (w) "[Hl HPhys]".
  (* We can now perform the load, and get rid of the modality. *)
  wp_load. iModIntro. iSplitL "Hl Hγ● HPhys"; first by eauto 10 with iFrame.
  (* We then resume stepping through the program, and focus on the CAS. *)
  wp_alloc r as "Hr". wp_inj. wp_bind (CmpXchg _ _ _)%E.
  (* Now, we need to use the invariant again to gain information on [ℓ]. *)
  iInv "HInv" as (ys) ">[HPhys Hγ●]". iDestruct "HPhys" as (u) "[Hl HPhys]".
  (* We now reason by case on the success/failure of the CAS. *)
  destruct (decide (u = w)) as [[= ->]|NE].
  - (* The CAS succeeded. *)
    wp_cmpxchg_suc. { case w; left; done. (* Administrative stuff. *) }
    (* This was the linearization point. We access the preconditon. *)
    iMod "AU" as (zs) "[Hγ◯ [_ HClose]]".
    (* Use agreement on ressource [γ] to learn [zs = ys]. *)
    iDestruct (auth_agree with "Hγ● Hγ◯") as %->.
    (* Update the value of [γ] to [v::zs]. *)
    iMod (auth_update γ (v::zs) with "Hγ● Hγ◯") as "[Hγ● Hγ◯]".
    (* Commit operation. *)
    iMod ("HClose" with "Hγ◯") as "H".
    (* We can eliminate the modality. *)
    iMod (mapsto_persist with "Hr") as "Hr".
    iModIntro. iSplitR "H"; first by eauto 10 with iFrame.
    (* And conclude the proof easily, after some computation steps. *)
    wp_pures. iExact "H".
  - (* The CAS failed. *)
    wp_cmpxchg_fail. { exact: not_inj.  }
    { case u, w; simpl; eauto. (* Administrative stuff. *) }
    (* We can eliminate the modality. *)
    iModIntro. iSplitL "Hγ● Hl HPhys"; first by eauto 10 with iFrame.
    (* And conclude the proof by induction hypothesis. *)
    wp_pures. iApply "IH". iExact "AU".
Qed.

(** As for [push_stack] the specification of [pop_stack] depends on a location
    [ℓ] and a name [γ] (corresponding to some stack). A logically atomic Hoare
    triple is again used to ensure linearizability, but it must be accessed in
    a slightly more complicated way. In particular, the linearization point is
    not in the same place depending on the emptiness of the stack.  Of course,
    the postcondition also depends on the emptiness of the stack. *)
Lemma pop_stack_spec (ℓ : loc) (γ : gname) :
  is_stack ℓ γ -∗
  <<< ∀∀ (xs : list val), stack_cont γ xs >>>
    pop_stack #ℓ @ ↑N
  <<< stack_cont γ (match xs with [] => [] | _::xs => xs end)
    , RET (match xs with [] => NONEV | v::_ => SOMEV v end) >>>.
Proof.
  (* As for [push_stack], we need to use induction and the focus on a load. *)
  iIntros "#HInv" (Φ) "AU". iLöb as "IH". wp_lam. wp_bind (! _)%E.
  (* We can then use the invariant to be able to perform the load. *)
  iInv "HInv" as (xs) ">[HPhys Hγ●]".
  iDestruct "HPhys" as (w) "[Hl #HPhys]". wp_load.
  (* We then inspect the contents of the stack and the optional location. They
     must agree, otherwise the proof is trivial. *)
  destruct w as [w|], xs as [|x xs]; try done; simpl.
  - (* The stack is non-empty, we eliminate the modality. *)
    iModIntro. iSplitL "Hl Hγ●"; first by eauto 10 with iFrame.
    (* We continue stepping through the program, and focus on the CAS. *)
    wp_let. wp_match. iDestruct "HPhys" as (r) "[Hw HP]".
    wp_load. wp_let. wp_proj. wp_bind (CmpXchg _ _ _)%E.
    (* We need to use the invariant again to gain information on [ℓ]. *)
    iInv "HInv" as (ys) ">[H Hγ●]".
    unfold phys_stack. iDestruct "H" as (u) "[Hl HPhys]".
    (* We get rid of useless hypotheses to cleanup the context. *)
    iClear "HP". clear xs.
    (* We reason by case on the success/failure of the CAS. *)
    destruct (decide (u = Some w)) as [[= ->]|Hx].
    * (* The CAS succeeded, so this is the linearization point. *)
      wp_cmpxchg_suc.
      (* The list [ys] must be non-empty, otherwise the proof is trivial. *)
      destruct ys as [|y ys]; first done.
      (* We access the precondition, prior to performing an update. *)
      iMod "AU" as (zs) "[Hγ◯ [_ HClose]]". unfold stack_cont.
      (* Use agreement on ressource [γ] to learn [v :: ys = zs]. *)
      iDestruct (auth_agree with "Hγ● Hγ◯") as %<-.
      (* Update the value of [γ] to [ys] (the tail of previous value). *)
      iMod (auth_update γ ys with "Hγ● Hγ◯") as "[Hγ● Hγ◯]".
      (* We need to learn that [r = u] (true since mapsto must agree). *)
      iDestruct "HPhys" as (u) "[Hw' HPhys]".
      iDestruct (mapsto_agree with "Hw Hw'") as %[=-> ->%to_val_inj].
      (* Perform the commit. *)
      iMod ("HClose" with "Hγ◯") as "HΦ".
      (* Eliminate the modality. *)
      iModIntro. iSplitR "HΦ"; first by eauto 10 with iFrame.
      (* And conclude the proof. *)
      wp_pures. iExact "HΦ".
    * (* The CAS failed. *)
      wp_cmpxchg_fail. { intro H. apply Hx. destruct u; inversion H; done. }
      (* We can eliminate the modality. *)
      iModIntro. iSplitR "AU"; first by eauto 10 with iFrame.
      (* And conclude the proof using the induction hypothesis. *)
      wp_pures. iApply "IH". iExact "AU".
  - (* The stack is empty, the load was the linearization point,  we can hence
       commit (without updating the stack). So we access the precondition. *)
    iMod "AU" as (xs) "[Hγ◯ [_ HClose]]".
    (* Thanks to agreement, we learn that [xs] must be the empty list. *)
    iDestruct (auth_agree with "Hγ● Hγ◯") as %<-.
    (* And we can commit (we are still at the linearization point). *)
    iMod ("HClose" with "Hγ◯") as "HΦ".
    (* We finally eliminate the modality and conclude the proof by taking some
       computation steps, and using our hypothesis. *)
    iModIntro. iSplitR "HΦ"; first by eauto 10 with iFrame.
    wp_pures. iExact "HΦ".
Qed.

End treiber_stack.

(** Make the exported Iris terms "Typeclass Opaque", so that clients using the
    library won't look into these definitions. *)
Global Typeclasses Opaque is_stack stack_cont.
