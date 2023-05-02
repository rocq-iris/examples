From iris.algebra Require Import excl auth agree frac list cmra csum.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris_examples.logatom.conditional_increment Require Import spec.
From iris.prelude Require Import options.

(** Using prophecy variables with helping: implementing conditional counter from
    "Logical Relations for Fine-Grained Concurrency" by Turon et al. (POPL 2013) *)

(** * Implementation of the functions. *)

(*
  new_counter() :=
    let c = ref (injL 0) in
    ref c
 *)
Definition new_counter : val :=
  λ: <>,
    ref (ref (InjL #0)).

(*
  complete(c, f, x, n, p) :=
    Resolve CmpXchg(c, x, ref (injL (if !f then n+1 else n))) p (ref ()) ;; ()
 *)
Definition complete : val :=
  λ: "c" "f" "x" "n" "p",
    let: "l_ghost" := ref #() in
    (* Compare with #true to make this a total operation that never
       gets stuck, no matter the value stored in [f]. *)
    let: "new_n" := if: !"f" = #true then "n" + #1 else "n" in
    Resolve (CmpXchg "c" "x" (ref (InjL "new_n"))) "p" "l_ghost" ;; #().

(*
  get c :=
    let x = !c in
    match !x with
    | injL n      => n
    | injR (f, n, p) => complete c f x n p; get(c, f)
 *)
Definition get : val :=
  rec: "get" "c" :=
    let: "x" := !"c" in
    match: !"x" with
      InjL "n"    => "n"
    | InjR "args" =>
        let: "f" := Fst (Fst "args") in
        let: "n" := Snd (Fst "args") in
        let: "p" := Snd "args" in
        complete "c" "f" "x" "n" "p" ;;
        "get" "c"
    end.

(*
  cinc c f :=
    let x = !c in
    match !x with
    | injL n =>
        let p := new proph in
        let y := ref (injR (n, f, p)) in
        if CAS(c, x, y) then complete(c, f, y, n, p)
        else cinc c f
    | injR (f', n', p') =>
        complete(c, f', x, n', p');
        cinc c f
 *)
Definition cinc : val :=
  rec: "cinc" "c" "f" :=
    let: "x" := !"c" in
    match: !"x" with
      InjL "n" =>
        let: "p" := NewProph in
        let: "y" := ref (InjR ("f", "n", "p")) in
        if: CAS "c" "x" "y" then complete "c" "f" "y" "n" "p" ;; Skip
        else "cinc" "c" "f"
    | InjR "args'" =>
        let: "f'" := Fst (Fst "args'") in
        let: "n'" := Snd (Fst "args'") in
        let: "p'" := Snd "args'" in
        complete "c" "f'" "x" "n'" "p'" ;;
        "cinc" "c" "f"
    end.

(** ** Proof setup *)

Definition numUR      := authR $ optionUR $ exclR ZO.
Definition tokenUR    := exclR unitO.
Definition one_shotUR := csumR (exclR unitO) (agreeR unitO).

Class cincG Σ := ConditionalIncrementG {
                     cinc_numG      :: inG Σ numUR;
                     cinc_tokenG    :: inG Σ tokenUR;
                     cinc_one_shotG :: inG Σ one_shotUR;
                   }.

Definition cincΣ : gFunctors :=
  #[GFunctor numUR; GFunctor tokenUR; GFunctor one_shotUR].

Global Instance subG_cincΣ {Σ} : subG cincΣ Σ → cincG Σ.
Proof. solve_inG. Qed.

Section conditional_counter.
  Context {Σ} `{!heapGS Σ, !cincG Σ}.
  Context (N : namespace).

  Local Definition stateN   := N .@ "state".
  Local Definition counterN := N .@ "counter".

  (** Updating and synchronizing the counter and flag RAs *)

  Lemma sync_counter_values γ_n (n m : Z) :
    own γ_n (● Excl' n) -∗ own γ_n (◯ Excl' m) -∗ ⌜n = m⌝.
  Proof.
    iIntros "H● H◯". iCombine "H●" "H◯" as "H". iDestruct (own_valid with "H") as "H".
      by iDestruct "H" as %[H%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  Qed.

  Lemma update_counter_value γ_n (n1 n2 m : Z) :
    own γ_n (● Excl' n1) -∗ own γ_n (◯ Excl' n2) ==∗ own γ_n (● Excl' m) ∗ own γ_n (◯ Excl' m).
  Proof.
    iIntros "H● H◯". iCombine "H●" "H◯" as "H". rewrite -own_op. iApply (own_update with "H").
    by apply auth_update, option_local_update, exclusive_local_update.
  Qed.

  Definition counter_content (γs : gname) (n : Z) :=
    (own γs (◯ Excl' n))%I.

  (** Definition of the invariant *)

  Fixpoint val_to_some_loc (vs : list (val * val)) : option loc :=
    match vs with
    | ((_, #true)%V, LitV (LitLoc l)) :: _  => Some l
    | _                         :: vs => val_to_some_loc vs
    | _                               => None
    end.

  Inductive abstract_state : Set :=
  | Quiescent : Z → abstract_state
  | Updating : loc → Z → proph_id → abstract_state.

  Definition state_to_val (s : abstract_state) : val :=
    match s with
    | Quiescent n => InjLV #n
    | Updating f n p => InjRV (#f,#n,#p)
    end.

  Global Instance state_to_val_inj : Inj (=) (=) state_to_val.
  Proof.
    intros [|] [|]; simpl; intros Hv; inversion_clear Hv; done.
  Qed.

  Definition own_token γ := (own γ (Excl ()))%I.

  Definition pending_state P (n : Z) (proph_winner : option loc) l_ghost_winner (γ_n : gname) :=
    (P ∗ ⌜match proph_winner with None => True | Some l => l = l_ghost_winner end⌝ ∗ own γ_n (● Excl' n))%I.

  (* After the prophecy said we are going to win the race, we commit and run the AU,
     switching from [pending] to [accepted]. *)
  Definition accepted_state Q (proph_winner : option loc) (l_ghost_winner : loc) :=
    ((∃ v, l_ghost_winner ↦{#1/2} v) ∗ match proph_winner with None => True | Some l => ⌜l = l_ghost_winner⌝ ∗ Q end)%I.

  (* The same thread then wins the CmpXchg and moves from [accepted] to [done].
     Then, the [γ_t] token guards the transition to take out [Q].
     Remember that the thread winning the CmpXchg might be just helping.  The token
     is owned by the thread whose request this is.
     In this state, [l_ghost_winner] serves as a token to make sure that
     only the CmpXchg winner can transition to here, and owning half of[l] serves as a
     "location" token to ensure there is no ABA going on. Notice how [counter_inv]
     owns *more than* half of its [l], which means we know that the [l] there
     and here cannot be the same. *)
  Definition done_state Q (l l_ghost_winner : loc) (γ_t : gname) :=
    ((Q ∨ own_token γ_t) ∗ (∃ v, l_ghost_winner ↦ v) ∗ (∃ v, l ↦{#1/2} v))%I.

  (* We always need the [proph] in here so that failing threads coming late can
     always resolve their stuff.
     Moreover, we need a way for anyone who has observed the [done] state to
     prove that we will always remain [done]; that's what the one-shot token [γ_s] is for. *)
  Definition state_inv P Q (p : proph_id) n (c_l l l_ghost_winner : loc) γ_n γ_t γ_s : iProp Σ :=
    (∃ vs, proph p vs ∗
      (own γ_s (Cinl $ Excl ()) ∗
       (c_l ↦{#1/2} #l ∗ ( pending_state P n (val_to_some_loc vs) l_ghost_winner γ_n
        ∨ accepted_state Q (val_to_some_loc vs) l_ghost_winner ))
       ∨ own γ_s (Cinr $ to_agree ()) ∗ done_state Q l l_ghost_winner γ_t))%I.

  Local Definition cinc_au Q γs f :=
    (AU << ∃∃ (b : bool) (n : Z), counter_content γs n ∗ f ↦_(λ _, True) #b >>
           @ ⊤∖(↑N ∪ ↑inv_heapN), ∅
        << counter_content γs (if b then n + 1 else n)%Z ∗ f ↦_(λ _, True) #b, COMM Q >>)%I.

  Definition counter_inv γ_n c :=
    (∃ (l : loc) (q : Qp) (s : abstract_state),
       (* We own *more than* half of [l], which shows that this cannot
          be the [l] of any [state] protocol in the [done] state. *)
       c ↦{#1/2} #l ∗ l ↦{#1/2 + q} (state_to_val s) ∗
       match s with
        | Quiescent n => c ↦{#1/2} #l ∗ own γ_n (● Excl' n)
        | Updating f n p =>
           ∃ Q l_ghost_winner γ_t γ_s,
             (* There are two pieces of per-[state]-protocol ghost state:
             - [γ_t] is a token owned by whoever created this protocol and used
               to get out the [Q] in the end.
             - [γ_s] reflects whether the protocol is [done] yet or not. *)
             inv stateN (state_inv (cinc_au Q γ_n f) Q p n c l l_ghost_winner γ_n γ_t γ_s) ∗
             f ↦_(λ _, True) □
       end)%I.

  Local Hint Extern 0 (environments.envs_entails _ (counter_inv _ _)) => unfold counter_inv : core.

  Definition is_counter (γ_n : gname) (ctr : val) :=
    (∃ (c : loc), ⌜ctr = #c ∧ N ## inv_heapN⌝ ∗ inv_heap_inv ∗ inv counterN (counter_inv γ_n c))%I.

  Global Instance is_counter_persistent γs ctr : Persistent (is_counter γs ctr) := _.

  Global Instance counter_content_timeless γs n : Timeless (counter_content γs n) := _.

  Global Instance abstract_state_inhabited: Inhabited abstract_state := populate (Quiescent 0).

  Lemma counter_content_exclusive γs c1 c2 :
    counter_content γs c1 -∗ counter_content γs c2 -∗ False.
  Proof.
    iIntros "Hb1 Hb2".
    iCombine "Hb1 Hb2" gives %?%auth_frag_op_valid_1.
    done.
  Qed.

  (** A few more helper lemmas that will come up later *)

  Lemma mapsto_valid_3 l v1 v2 q :
    l ↦ v1 -∗ l ↦{q} v2 -∗ ⌜False⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (mapsto_ne with "Hl1 Hl2") as %?; done.
  Qed.

  (** Once a [state] protocol is [done] (as reflected by the [γ_s] token here),
      we can at any later point in time extract the [Q]. *)
  Lemma state_done_extract_Q P Q p m c_l l l_ghost γ_n γ_t γ_s :
    inv stateN (state_inv P Q p m c_l l l_ghost γ_n γ_t γ_s) -∗
    own γ_s (Cinr (to_agree ())) -∗
    □(own_token γ_t ={⊤}=∗ ▷ Q).
  Proof.
    iIntros "#Hinv #Hs !# Ht".
    iInv stateN as (vs) "(Hp & [NotDone | Done])".
    * (* Moved back to NotDone: contradiction. *)
      iDestruct "NotDone" as "(>Hs' & _ & _)".
      iCombine "Hs Hs'" gives %?. contradiction.
    * iDestruct "Done" as "(_ & QT & Hghost)".
      iDestruct "QT" as "[Q | >T]"; last first.
      { iCombine "Ht T" gives %Contra.
          by inversion Contra. }
      iSplitR "Q"; last done. iIntros "!> !>". unfold state_inv.
      iExists _. iFrame "Hp". iRight.
      unfold done_state. iFrame "#∗".
  Qed.

  (** ** Proof of [complete] *)

  (** The part of [complete] for the succeeding thread that moves from [accepted] to [done] state *)
  Lemma complete_succeeding_thread_pending (γ_n γ_t γ_s : gname) c_l P Q p
        (m n : Z) (l l_ghost l_new : loc) Φ :
    inv counterN (counter_inv γ_n c_l) -∗
    inv stateN (state_inv P Q p m c_l l l_ghost γ_n γ_t γ_s) -∗
    l_ghost ↦{# 1 / 2} #() -∗
    (□(own_token γ_t ={⊤}=∗ ▷ Q) -∗ Φ #()) -∗
    own γ_n (● Excl' n) -∗
    l_new ↦ InjLV #n -∗
    WP Resolve (CmpXchg #c_l #l #l_new) #p #l_ghost ;; #() {{ v, Φ v }}.
  Proof.
    iIntros "#InvC #InvS Hl_ghost HQ Hn● [Hl_new Hl_new']". wp_bind (Resolve _ _ _)%E.
    iInv counterN as (l' q s) "(>Hc & >[Hl Hl'] & Hrest)".
    iInv stateN as (vs) "(>Hp & [NotDone | Done])"; last first.
    { (* We cannot be [done] yet, as we own the "ghost location" that serves
         as token for that transition. *)
      iDestruct "Done" as "(_ & _ & Hlghost & _)".
      iDestruct "Hlghost" as (v') ">Hlghost".
        by iCombine "Hl_ghost Hlghost" gives %[??].
    }
    iDestruct "NotDone" as "(>Hs & >Hc' & [Pending | Accepted])".
    { (* We also cannot be [Pending] any more we have [own γ_n] showing that this
       transition has happened   *)
       iDestruct "Pending" as "[_ >[_ Hn●']]".
       iCombine "Hn●" "Hn●'" as "Contra".
       iDestruct (own_valid with "Contra") as %Contra. by inversion Contra.
    }
    (* So, we are [Accepted]. Now we can show that l = l', because
       while a [state] protocol is not [done], it owns enough of
       the [counter] protocol to ensure that does not move anywhere else. *)
    iDestruct (mapsto_agree with "Hc Hc'") as %[= ->].
    (* We perform the CmpXchg. *)
    iCombine "Hc Hc'" as "Hc".
    wp_apply (wp_resolve with "Hp"); first done; wp_cmpxchg_suc.
    iIntros "!>" (vs' ->) "Hp'". simpl.
    (* Update to Done. *)
    iDestruct "Accepted" as "[Hl_ghost_inv [HEq Q]]".
    iMod (own_update with "Hs") as "Hs".
    { apply (cmra_update_exclusive (Cinr (to_agree ()))). done. }
    iDestruct "Hs" as "#Hs'". iModIntro.
    iSplitL "Hl_ghost_inv Hl_ghost Q Hp' Hl".
    (* Update state to Done. *)
    { iNext. iExists _. iFrame "Hp'". iRight. unfold done_state.
      iFrame "#∗". iDestruct "Hl_ghost_inv" as (v) "Hl_ghost_inv".
      iDestruct (mapsto_agree with "Hl_ghost Hl_ghost_inv") as %<-.
      iSplitR "Hl"; iExists _; iFrame. }
    iModIntro. iSplitR "HQ".
    { iNext. iDestruct "Hc" as "[Hc1 Hc2]".
      iExists l_new, _, (Quiescent n). iFrame. }
    wp_seq. iApply "HQ".
    iApply state_done_extract_Q; done.
  Qed.

  (** The part of [complete] for the failing thread *)
  Lemma complete_failing_thread γ_n γ_t γ_s c_l l P Q p m n l_ghost_inv l_ghost l_new Φ :
    l_ghost_inv ≠ l_ghost →
    inv counterN (counter_inv γ_n c_l) -∗
    inv stateN (state_inv P Q p m c_l l l_ghost_inv γ_n γ_t γ_s) -∗
    (□(own_token γ_t ={⊤}=∗ ▷ Q) -∗ Φ #()) -∗
    l_new ↦ InjLV #n -∗
    WP Resolve (CmpXchg #c_l #l #l_new) #p #l_ghost ;; #() {{ v, Φ v }}.
  Proof.
    iIntros (Hnl) "#InvC #InvS HQ Hl_new". wp_bind (Resolve _ _ _)%E.
    iInv counterN as (l' q s) "(>Hc & >[Hl Hl'] & Hrest)".
    iInv stateN as (vs) "(>Hp & [NotDone | [#Hs Done]])".
    { (* If the [state] protocol is not done yet, we can show that it
         is the active protocol still (l = l').  But then the CmpXchg would
         succeed, and our prophecy would have told us that.
         So here we can prove that the prophecy was wrong. *)
        iDestruct "NotDone" as "(_ & >Hc' & State)".
        iDestruct (mapsto_agree with "Hc Hc'") as %[=->].
        iCombine "Hc Hc'" as "Hc".
        wp_apply (wp_resolve with "Hp"); first done; wp_cmpxchg_suc.
        iIntros "!>" (vs' ->). iDestruct "State" as "[Pending | Accepted]".
        + iDestruct "Pending" as "[_ [Hvs _]]". iDestruct "Hvs" as %Hvs. by inversion Hvs.
        + iDestruct "Accepted" as "[_ [Hvs _]]". iDestruct "Hvs" as %Hvs. by inversion Hvs. }
    (* So, we know our protocol is [Done]. *)
    (* It must be that l' ≠ l because we are in the failing thread. *)
    destruct (decide (l' = l)) as [->|Hn]. {
      (* The [state] protocol is [done] while still being the active protocol
         of the [counter]?  Impossible, now we will own more than the whole location! *)
      iDestruct "Done" as "(_ & _ & >Hl'')".
      iDestruct "Hl''" as (v') "Hl''".
      iDestruct (mapsto_combine with "Hl Hl''") as "[Hl _]".
      rewrite dfrac_op_own Qp.half_half.
      iDestruct (mapsto_valid_3 with "Hl Hl'") as "[]".
    }
    (* The CmpXchg fails. *)
    wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_fail.
    iIntros "!>" (vs' ->) "Hp". iModIntro.
    iSplitL "Done Hp". { iNext. iExists _. iFrame "#∗". } iModIntro.
    iSplitL "Hc Hrest Hl Hl'". { eauto 10 with iFrame. }
    wp_seq. iApply "HQ".
    iApply state_done_extract_Q; done.
  Qed.

  (** ** Proof of [complete] *)
  (* The postcondition basically says that *if* you were the thread to own
     this request, then you get [Q].  But we also try to complete other
     thread's requests, which is why we cannot ask for the token
     as a precondition. *)
  Lemma complete_spec (c f l : loc) (n : Z) (p : proph_id) γ_n γ_t γ_s l_ghost_inv Q :
    N ## inv_heapN →
    inv_heap_inv -∗
    inv counterN (counter_inv γ_n c) -∗
    inv stateN (state_inv (cinc_au Q γ_n f) Q p n c l l_ghost_inv γ_n γ_t γ_s) -∗
    f ↦_(λ _, True) □ -∗
    {{{ True }}}
       complete #c #f #l #n #p
    {{{ RET #(); □ (own_token γ_t ={⊤}=∗ ▷Q) }}}.
  Proof.
    iIntros (?) "#GC #InvC #InvS #isGC".
    iModIntro. iIntros (Φ) "_ HQ". wp_lam. wp_pures.
    wp_alloc l_ghost as "[Hl_ghost' Hl_ghost'2]".
    wp_pure credit:"Hlc". wp_pures.
    wp_bind (! _)%E. simpl.
    (* open outer invariant *)
    iInv counterN as (l' q s) "(>Hc & >Hl' & Hrest)".
    (* two different proofs depending on whether we are succeeding thread *)
    destruct (decide (l_ghost_inv = l_ghost)) as [-> | Hnl].
    - (* we are the succeeding thread *)
      (* we need to move from [pending] to [accepted]. *)
      iInv stateN as (vs) "(>Hp & [(>Hs & >Hc' & [Pending | Accepted]) | [#Hs Done]])".
      + (* Pending: update to accepted *)
        iDestruct "Pending" as "[AU >[Hvs Hn●]]".
        iMod (lc_fupd_elim_later with "Hlc AU") as "AU".
        iMod (inv_mapsto_own_acc_strong with "GC") as "Hgc"; first solve_ndisj.
        (* open and *COMMIT* AU, sync flag and counter *)
        iMod "AU" as (b n2) "[[Hn◯ Hf] [_ Hclose]]".
        iDestruct ("Hgc" with "Hf") as "(_ & Hf & Hfclose)".
        wp_load.
        iMod ("Hfclose" with "[//] Hf") as "[Hf Hfclose]".
        iDestruct (sync_counter_values with "Hn● Hn◯") as %->.
        iMod (update_counter_value _ _ _ (if b then n2 + 1 else n2)%Z with "Hn● Hn◯")
          as "[Hn● Hn◯]".
        iMod ("Hclose" with "[Hn◯ Hf]") as "Q"; first by iFrame.
        iModIntro. iMod "Hfclose" as "_".
        (* close state inv *)
        iIntros "!> !>". iSplitL "Q Hl_ghost' Hp Hvs Hs Hc'".
        { iNext. iExists _. iFrame "Hp". iLeft. iFrame.
          iRight. iSplitL "Hl_ghost'"; first by iExists _.
          destruct (val_to_some_loc vs) eqn:Hvts; iFrame. }
        (* close outer inv *)
        iModIntro. iSplitR "Hl_ghost'2 HQ Hn●".
        { eauto 12 with iFrame. }
        destruct b;
        wp_alloc l_new as "Hl_new"; wp_pures;
          iApply (complete_succeeding_thread_pending
                    with "InvC InvS Hl_ghost'2 HQ Hn● Hl_new").
      + (* Accepted: contradiction *)
        iDestruct "Accepted" as "[>Hl_ghost_inv _]".
        iDestruct "Hl_ghost_inv" as (v) "Hlghost".
        iCombine "Hl_ghost'" "Hl_ghost'2" as "Hl_ghost'".
        by iCombine "Hlghost Hl_ghost'" gives %[??].
      + (* Done: contradiction *)
        iDestruct "Done" as "[QT >[Hlghost _]]".
        iDestruct "Hlghost" as (v) "Hlghost".
        iCombine "Hl_ghost'" "Hl_ghost'2" as "Hl_ghost'".
        by iCombine "Hlghost Hl_ghost'" gives %[??].
    - (* we are the failing thread. exploit that [f] is a GC location. *)
      iMod (inv_mapsto_acc with "GC isGC") as (b) "(_ & H↦ & Hclose)"; first solve_ndisj.
      wp_load.
      iMod ("Hclose" with "H↦") as "_". iModIntro.
      (* close invariant *)
      iModIntro. iSplitL "Hc Hrest Hl'". { eauto 10 with iFrame. }
      (* two equal proofs depending on value of b1 *)
      wp_pures.
      destruct (bool_decide (b = #true));
      wp_alloc Hl_new as "Hl_new"; wp_pures;
        iApply (complete_failing_thread
                  with "InvC InvS HQ Hl_new"); done.
  Qed.

  (** ** Proof of [cinc] *)

  Lemma cinc_spec γs v (f: loc) :
    is_counter γs v -∗
    <<< ∀∀ (b : bool) (n : Z), counter_content γs n ∗ f ↦_(λ _, True) #b >>>
        cinc v #f @ (↑N ∪ ↑inv_heapN)
    <<< counter_content γs (if b then n + 1 else n)%Z ∗ f ↦_(λ _, True) #b, RET #() >>>.
  Proof.
    iIntros "#InvC". iDestruct "InvC" as (c_l [-> ?]) "[#GC #InvC]".
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_pures. wp_bind (!_)%E.
    iInv counterN as (l' q s) "(>Hc & >[Hl [Hl' Hl'']] & Hrest)".
    wp_load. destruct s as [n|f' n' p'].
    - iDestruct "Hrest" as "(Hc' & Hv)".
      iModIntro. iSplitR "AU Hl'".
      { iModIntro. iExists _, (q/2)%Qp, (Quiescent n). iFrame. }
      wp_let. wp_load. wp_match. wp_apply wp_new_proph; first done.
      iIntros (l_ghost p') "Hp'".
      wp_let. wp_alloc ly as "Hly".
      wp_let. wp_bind (CmpXchg _ _ _)%E.
      (* open outer invariant again to CAS c_l *)
      iInv counterN as (l'' q2 s) "(>Hc & >Hl & Hrest)".
      destruct (decide (l' = l'')) as [<- | Hn].
      + (* CAS succeeds *)
        iDestruct (mapsto_agree with "Hl' Hl") as %<-%state_to_val_inj.
        iDestruct "Hrest" as ">[Hc' Hn●]". iCombine "Hc Hc'" as "Hc".
        wp_cmpxchg_suc.
        (* Take a "peek" at [AU] and abort immediately to get [gc_is_gc f]. *)
        iMod "AU" as (b' n') "[[CC Hf] [Hclose _]]".
        iDestruct (inv_mapsto_own_inv with "Hf") as "#Hgc".
        iMod ("Hclose" with "[CC Hf]") as "AU"; first by iFrame.
        (* Initialize new [state] protocol .*)
        iMod (own_alloc (Excl ())) as (γ_t) "Token"; first done.
        iMod (own_alloc (Cinl $ Excl ())) as (γ_s) "Hs"; first done.
        iDestruct "Hc" as "[Hc Hc']".
        set (winner := default ly (val_to_some_loc l_ghost)).
        iMod (inv_alloc stateN _ (state_inv _ _ _ _ _ _ winner _ _ _)
               with "[AU Hs Hp' Hc' Hn●]") as "#Hinv".
        { iNext. iExists _. iFrame "Hp'". iLeft. iFrame. iLeft.
          iFrame. destruct (val_to_some_loc l_ghost); simpl; (iSplit; last done); iExact "AU". }
        iModIntro. iDestruct "Hly" as "[Hly1 Hly2]". iSplitR "Hl' Token". {
          (* close invariant *)
          iNext. iExists _, _, (Updating f n p'). eauto 10 with iFrame.
        }
        wp_pures. wp_apply complete_spec; [done..|].
        iIntros "Ht". iMod ("Ht" with "Token") as "Φ". wp_seq. by wp_lam.
      + (* CAS fails: closing invariant and invoking IH *)
        wp_cmpxchg_fail.
        iModIntro. iSplitR "AU".
        { iModIntro. iExists _, _, s. iFrame. }
        wp_pures. by iApply "IH".
    - (* l' ↦ injR *)
      iModIntro.
      (* extract state invariant *)
      iDestruct "Hrest" as (Q l_ghost γ_t γ_s) "(#InvS & #Hgc)".
      iSplitR "Hl' AU".
      (* close invariant *)
      { iModIntro. iExists _, _, (Updating f' n' p'). iFrame. eauto 10 with iFrame. }
      wp_let. wp_load. wp_match. wp_pures.
      wp_apply complete_spec; [done..|].
      iIntros "_". wp_seq. by iApply "IH".
  Qed.

  Lemma new_counter_spec :
    N ## inv_heapN →
    inv_heap_inv -∗
    {{{ True }}}
        new_counter #()
    {{{ ctr γs, RET ctr ; is_counter γs ctr ∗ counter_content γs 0 }}}.
  Proof.
    iIntros (?) "#GC". iIntros (Φ) "!# _ HΦ". wp_lam.
    wp_alloc l_n as "Hl_n".
    wp_alloc l_c as "Hl_c".
    iMod (own_alloc (● Excl' 0%Z  ⋅ ◯ Excl' 0%Z)) as (γ_n) "[Hn● Hn◯]".
    { by apply auth_both_valid_discrete. }
    iMod (inv_alloc counterN _ (counter_inv γ_n l_c)
      with "[Hl_c Hl_n Hn●]") as "#InvC".
    { iNext. iDestruct "Hl_c" as "[Hl_c1 Hl_c2]".
      iDestruct "Hl_n" as "[??]".
      iExists l_n, (1/2)%Qp, (Quiescent 0). iFrame. }
    iModIntro.
    iApply ("HΦ" $! #l_c γ_n).
    iSplitR; last by iFrame. iExists _. eauto with iFrame.
  Qed.

  Lemma get_spec γs v :
    is_counter γs v -∗
    <<< ∀∀ (n : Z), counter_content γs n >>>
        get v @ (↑N ∪ ↑inv_heapN)
    <<< counter_content γs n, RET #n >>>.
  Proof.
    iIntros "#InvC" (Φ) "AU". iDestruct "InvC" as (c_l [-> ?]) "[GC InvC]".
    iLöb as "IH". wp_lam. wp_bind (! _)%E.
    iInv counterN as (c q s) "(>Hc & >[Hl [Hl' Hl'']] & Hrest)".
    wp_load.
    destruct s as [n|f n p].
    - iMod "AU" as (au_n) "[Hn◯ [_ Hclose]]"; simpl.
      iDestruct "Hrest" as "[Hc' Hn●]".
      iDestruct (sync_counter_values with "Hn● Hn◯") as %->.
      iMod ("Hclose" with "Hn◯") as "HΦ".
      iModIntro. iSplitR "HΦ Hl'". {
        iNext. iExists c, (q/2)%Qp, (Quiescent au_n). iFrame.
      }
      wp_let. wp_load. wp_match. iApply "HΦ".
    - iDestruct "Hrest" as (Q l_ghost γ_t γ_s) "(#InvS & #Hgc)".
      iModIntro. iSplitR "AU Hl'". {
        iNext. iExists c, (q/2)%Qp, (Updating _ _ p). eauto 10 with iFrame.
      }
      wp_let. wp_load. wp_pures. wp_bind (complete _ _ _ _ _)%E.
      wp_apply complete_spec; [done..|].
      iIntros "Ht". wp_seq. iApply "IH". iApply "AU".
  Qed.

End conditional_counter.

Definition atomic_cinc `{!heapGS Σ, !cincG Σ} :
  spec.atomic_cinc Σ :=
  {| spec.new_counter_spec := new_counter_spec;
     spec.cinc_spec := cinc_spec;
     spec.get_spec := get_spec;
     spec.counter_content_exclusive := counter_content_exclusive |}.

Global Typeclasses Opaque counter_content is_counter.
