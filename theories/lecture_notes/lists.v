(* In this file we explain how to do the "list examples" from the
   Chapter on Separation Logic for Sequential Programs in the
   Iris Lecture Notes *)


(* Contains definitions of the weakest precondition assertion, and its basic rules. *)
From iris.program_logic Require Export weakestpre.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Export notation lang.

(* Files related to the interactive proof mode. The first import includes the
   general tactics of the proof mode. The second provides some more specialized
   tactics particular to the instantiation of Iris to a particular programming
   language. *)
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.

(* The following line imports some Coq configuration we commonly use in Iris
   projects, mostly with the goal of catching common mistakes. *)

(*  ---------------------------------------------------------------------- *)

Section list_model.
  (* This section contains the definition of our model of lists, i.e.,
     definitions relating pointer data structures to our model, which is
     simply mathematical sequences (Coq lists). *)


(* In order to do the proof we need to assume certain things about the
   instantiation of Iris. The particular, even the heap is handled in an
   analogous way as other ghost state. This line states that we assume the
   Iris instantiation has sufficient structure to manipulate the heap, e.g.,
   it allows us to use the points-to predicate. *)
Context `{!heapGS Σ}.
Implicit Types l : loc.

(* The variable Σ has to do with what ghost state is available, and the type
     of Iris propositions (written Prop in the lecture notes) depends on this Σ.
     But since Σ is the same throughout the development we shall define
     shorthand notation which hides it. *)
Notation iProp := (iProp Σ).

(* Here is the basic is_list representation predicate:
    is_list hd xs holds if hd points to a linked list consisting of
   the elements in the mathematical sequence (Coq list) xs.
 *)
Fixpoint is_list (hd : val) (xs : list val) : iProp :=
  match xs with
  | [] => ⌜hd = NONEV⌝
  | x :: xs => ∃ l hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x,hd') ∗ is_list hd' xs
end%I.

(* The following predicate
     is_listP P hd xs
   holds if hd points to a linked list consisting of the elements in xs and
   each of those elements satisfy P.
 *)
Fixpoint is_listP P (hd : val) (xs : list val) : iProp :=
  match xs with
  | [] => ⌜hd = NONEV⌝
  | x :: xs => ∃ l hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x,hd') ∗ is_listP P hd' xs ∗ P x
end%I.

(* about_isList expresses how is_listP P hd xs can be seen as a combination of the
   basic is_list predicate and the property that P holds for all the elements in xs.
 *)
Lemma about_isList P hd xs :
  is_listP P hd xs ⊣⊢ is_list hd xs ∗ [∗ list] x ∈ xs, P x.
Proof.
  generalize dependent hd.
  induction xs as [| x xs' IHxs]; simpl; intros hd; iSplit.
  - eauto.
  - by iIntros "(? & _)".
  - iDestruct 1 as (l hd') "(? & ? & H & ?)". rewrite IHxs. iDestruct "H" as "(H_isListxs' & ?)".
    iFrame.
  - iDestruct 1 as "(H_isList & ? & H)". iDestruct "H_isList" as (l hd') "(? & ? & ?)".
    iFrame. rewrite IHxs. iFrame.
Qed.

(* The predicate
      is_list_nat hd xs
   holds if hd is a pointer to a linked list of numbers (integers).
*)
Fixpoint is_list_nat (hd : val) (xs : list Z) : iProp :=
  match xs with
  | [] => ⌜hd = NONEV⌝
  | x :: xs => ∃ l hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (#x,hd') ∗ is_list_nat hd' xs
  end%I.


(* The reverse function on Coq lists is defined in the Coq library. *)
Definition reverse (l : list val) := List.rev l.

Definition inj {A B : Type} (f : A -> B) : Prop :=
  forall (x y : A),
    f x = f y -> x = y.

Lemma map_injective {A B : Type} :
  forall xs ys (f : A -> B), inj f -> map f xs = map f ys
           -> xs = ys.
Proof.
  intros xs. induction xs as [|x xs IHxs]; intros ys f H_f H_map.
  - symmetry in H_map. by apply map_eq_nil in H_map.
  - destruct ys as [|y ys].
    + by apply map_eq_nil in H_map.
    + specialize (IHxs ys f). inversion H_map as [H_a].
      rewrite -> IHxs; try done.
      apply H_f in H_a. by rewrite H_a.
Qed.


End list_model.

(*  ---------------------------------------------------------------------- *)

Section list_code.
  (* This section contains the code of the list functions we specify *)

  (* Function inc hd assumes all values in the linked list pointed to by hd
     are numbers and increments them by 1, in-place *)
  Definition inc : val :=
  rec: "inc" "hd" :=
    match: "hd" with
      NONE => #()
    | SOME "l" =>
       let: "tmp1" := Fst !"l" in
       let: "tmp2" := Snd !"l" in
       "l" <- (("tmp1" + #1), "tmp2");;
       "inc" "tmp2"
    end.

  (* Function app l l' appends linked list l' to end of linked list l *)
  Definition app : val :=
  rec: "app" "l" "l'" :=
    match: "l" with
      NONE => "l'"
    | SOME "hd" =>
      let: "tmp1" := !"hd" in
      let: "tmp2" := "app" (Snd "tmp1") "l'" in
      "hd" <- ((Fst "tmp1"), "tmp2");;
           "l"
    end.

  (* Function rev l acc reverses all the pointers in linked list l and stiches
     the accumulator argument acc at the end *)
  Definition rev : val :=
  rec: "rev" "l" "acc" :=
    match: "l" with
      NONE => "acc"
    | SOME "p" =>
       let: "h" := Fst !"p" in
       let: "t" := Snd !"p" in
       "p" <- ("h", "acc");;
       "rev" "t" "l"
    end.

  (* Function len l returns the lenght of linked list l *)
  Definition len : val :=
  rec: "len" "l" :=
    match: "l" with
      NONE => #0
    | SOME "p" =>
      ("len" (Snd !"p") + #1)
    end.

  (* Function foldr f a l is the usual fold right function for linked list l, with
     base value a and combination function f *)
  Definition foldr : val :=
  rec: "foldr" "f" "a" "l" :=
    match: "l" with
      NONE => "a"
    | SOME "p" =>
      let: "hd" := Fst !"p" in
      let: "t" := Snd !"p" in
      "f" ("hd", ("foldr" "f" "a" "t"))
    end.

  (* sum_list l returns the sum of the list of numbers in linked list l,
     implemented by call to foldr *)
  Definition sum_list : val :=
  rec: "sum_list" "l" :=
    let: "f'" := (λ: "p", let: "x" := Fst "p" in
                         let: "y" := Snd "p" in
                         "x" + "y")
    in
    (foldr  "f'" #0 "l").

  Definition cons : val := (λ: "x" "xs",
                          let: "p" := ("x", "xs") in
                          SOME (Alloc("p"))).

  Definition empty_list : val := NONEV.

  (* filter prop l is the usual filter function on linked lists, prop is supposed
     to be a function from values to booleans. Implemented using foldr. *)
  Definition filter : val :=
  rec: "filter" "prop" "l" :=
    let: "f" :=  (λ: "p",
                  let: "x" := Fst "p" in
                  let: "xs" := Snd "p" in
                  if: ("prop" "x")
                  then (cons "x" "xs")
                  else "xs")
    in (foldr "f" empty_list "l").

  (* map_list f l is the usual map function on linked lists with f the function
     to be mapped over the list l. Implemented using foldr. *)
  Definition map_list : val :=
  rec: "map_list" "f" "l" :=
    let: "f'" :=  (λ: "p",
                   let: "x" := Fst "p" in
                   let: "xs" := Snd "p" in
                   (cons ("f" "x") "xs"))
    in
    (foldr "f'" empty_list "l").

  (* incr l is another variant of the increment function on linked lists, implemented using map. *)
  Definition incr : val :=
    rec: "incr" "l" :=
     map_list (λ: "n", "n" + #1)%I "l".

End list_code.

(*  ---------------------------------------------------------------------- *)

Section list_spec.
  (* This section contains the specifications and proofs for the list functions.
     The specifications and proofs are explained in the Iris Lecture Notes
   *)

  Context `{!heapGS Σ}.

Lemma inc_spec hd xs :
  {{{ is_list_nat hd xs }}}
    inc hd
  {{{ w, RET w; ⌜w = #()⌝ ∗ is_list_nat hd (List.map Z.succ xs) }}}.
Proof.
  iIntros (ϕ) "Hxs H".
  iLöb as "IH" forall (hd xs ϕ). wp_rec. destruct xs as [|x xs]; iSimplifyEq.
   - wp_match. iApply "H". done.
   - iDestruct "Hxs" as (l hd') "(% & Hx & Hxs)". iSimplifyEq.
     wp_match. do 2 (wp_load; wp_proj; wp_let). wp_op.
     wp_store. iApply ("IH" with "Hxs").
     iNext. iIntros (w) "H'". iApply "H". iDestruct "H'" as "[Hw Hislist]".
     iFrame. done.
Qed.


Lemma app_spec xs ys (l l' : val) :
  {{{ is_list l xs ∗ is_list l' ys }}}
    app l l'
  {{{ v, RET v; is_list v (xs ++ ys) }}}.
Proof.
  iIntros (ϕ) "[Hxs Hys] H".
  iLöb as "IH" forall (l xs l' ys ϕ).
  destruct xs as [| x xs']; iSimplifyEq.
   - wp_rec. wp_let. wp_match. iApply "H". done.
   - iDestruct "Hxs" as (l0 hd0) "(% & Hx & Hxs)". iSimplifyEq.
     wp_rec. wp_let. wp_match. wp_load. wp_let. wp_proj. wp_bind (app _ _)%E.
     iApply ("IH" with "Hxs Hys").
     iNext. iIntros (v) "?". wp_let. wp_proj. wp_store. iSimplifyEq. iApply "H".
     iExists l0, _. iFrame. done.
Qed.


Lemma rev_spec vs us (l acc : val) :
  {{{ is_list l vs ∗ is_list acc us }}}
    rev l acc
  {{{ w, RET w; is_list w (reverse vs ++ us) }}}.
Proof.
  iIntros (ϕ) "[H1 H2] HL".
  iInduction vs as [| v vs'] "IH" forall (acc l us).
   - iSimplifyEq. wp_rec. wp_let. wp_match. iApply "HL". done.
   - simpl. iDestruct "H1" as (l' t) "(%H & H3 & H1)". wp_rec. wp_let.
     rewrite -> H at 1. wp_match. do 2 (wp_load; wp_proj; wp_let).
     wp_store. iSpecialize ("IH" $! l t ([v] ++ us)).
     iApply ("IH" with "[H1] [H3 H2]").
     + done.
     + simpl. iExists l', acc. iFrame. done.
     + iNext. rewrite -> app_assoc. done.
Qed.

Lemma len_spec (l : val) xs :
  {{{ is_list l xs }}}
    len l
  {{{ v, RET v; ⌜v = #(length xs)⌝ }}}.
Proof.
  iIntros (ϕ) "Hl H".
  iInduction xs as [| x xs'] "IH" forall (l ϕ); iSimplifyEq.
   - wp_rec. wp_match. iApply "H". done.
   - iDestruct "Hl" as (p hd') "(% & Hp & Hhd')". wp_rec. iSimplifyEq.
     wp_match. wp_load. wp_proj. wp_bind (len hd')%I. iApply ("IH" with "[Hhd'] [Hp H]"); try done.
     iNext. iIntros. iSimplifyEq. wp_op. iApply "H". iPureIntro. do 2 f_equal. lia.
Qed.

(* The following specifications for foldr are non-trivial because the code is higher-order
   and hence the specifications involve nested triples.
   The specifications are explained in the Iris Lecture Notes. *)


Lemma foldr_spec_PI P I  (f a hd : val) (xs : list val) :
  {{{ (∀ (x a' : val) (ys : list val),
          {{{ P x ∗ I ys a'}}}
            f (x, a')
          {{{r, RET r; I (x::ys) r }}})
        ∗ is_list hd xs
        ∗ ([∗ list] x ∈ xs, P x)
        ∗ I [] a
  }}}
    foldr f a hd
  {{{
       r, RET r; is_list hd xs
                 ∗ I xs r
  }}}.
Proof.
  iIntros (ϕ) "(#H_f & H_isList & H_Px & H_Iempty) H_inv".
  iInduction xs as [|x xs'] "IH" forall (ϕ a hd); wp_rec; do 2 wp_let; iSimplifyEq.
  - wp_match. iApply "H_inv". eauto.
  - iDestruct "H_isList" as (l hd') "[% [H_l H_isList]]".
    iSimplifyEq.
    wp_match. do 2 (wp_load; wp_proj; wp_let).
    wp_bind (((foldr f) a) hd').
    iDestruct "H_Px" as "(H_Px & H_Pxs')".
    iApply ("IH" with "H_isList H_Pxs' H_Iempty [H_l H_Px H_inv]").
    iNext. iIntros (r) "(H_isListxs' & H_Ixs')".
    iApply ("H_f" with "[$H_Ixs' $H_Px] [H_inv H_isListxs' H_l]").
    iNext. iIntros (r') "H_inv'". iApply "H_inv". iFrame. done.
Qed.

Lemma foldr_spec_PPI P I (f a hd : val) (xs : list val) :
  {{{ (∀ (x a' : val) (ys : list val),
          {{{ P x ∗ I ys a'}}}
            f (x, a')
          {{{r, RET r; I (x::ys) r }}})
        ∗ is_listP P hd xs
        ∗ I [] a
  }}}
    foldr f a hd
  {{{
       r, RET r; is_listP (fun x => True) hd xs
                 ∗ I xs r
  }}}.
Proof.
  iIntros (ϕ) "(#H_f & H_isList & H_Iempty) H_inv".
  rewrite about_isList. iDestruct "H_isList" as "(H_isList & H_Pxs)".
  iApply (foldr_spec_PI with "[-H_inv]").
  - iFrame. by iFrame "H_f".
  - iNext. iIntros (r) "(H_isList & H_Ixs)".
    iApply "H_inv". iFrame. rewrite about_isList. iFrame. by rewrite big_sepL_forall.
Qed.

Lemma sum_spec (hd: val) (xs: list Z) :
  {{{ is_list hd (map (fun (n : Z) => #n) xs)}}}
    sum_list hd
  {{{ v, RET v; ⌜v = # (fold_right Z.add 0 xs)⌝ }}}.
Proof.
  iIntros (ϕ) "H_is_list H_later".
  wp_rec. wp_pures.
  iApply (foldr_spec_PI
            (fun x => (∃ (n : Z), ⌜x = #n⌝)%I)
            (fun xs' acc => ∃ ys,
                 ⌜acc = #(fold_right Z.add 0 ys)⌝
               ∗ ⌜xs' = map (fun (n : Z) => #n) ys⌝
               ∗ ([∗ list] x ∈ xs',∃ (n' : Z), ⌜x = #n'⌝))%I
            with "[$H_is_list] [H_later]").
  - iSplitR.
    + iIntros (x a' ys). iModIntro. iIntros (ϕ') "(H1 & H2) H3".
      do 5 (wp_pure _).
      iDestruct "H2" as (zs) "(% & % & H_list)".
      iDestruct "H1" as (n2) "%". iSimplifyEq. wp_pures. iModIntro.
      iApply "H3". iExists (n2::zs). repeat (iSplit; try done).
      by iExists _.
    + iSplit.
      * induction xs as [|x xs IHxs]; iSimplifyEq; first done.
        iSplit; [iExists _; done | apply IHxs].
      * iExists []. eauto.
  - iNext. iIntros (r) "(H1 & H2)".
    iApply "H_later". iDestruct "H2" as (ys) "(% & % & H_list)".
    iSimplifyEq. rewrite (map_injective xs ys (λ n : Z, #n)); try done.
    unfold inj. intros x y H_xy. by inversion H_xy.
Qed.


Lemma filter_spec (hd p : val) (xs : list val) (R : val -> bool) (Q : val → iProp Σ) :
  {{{ is_list hd xs
      ∗ (∀ x : val ,
           {{{ Q x }}}
           p x
           {{{r, RET r; ⌜r = #(R x)⌝ }}}) ∗ [∗ list] x ∈ xs, Q x
  }}}
  filter p hd
  {{{ v, RET v; is_list hd xs
                ∗ is_list v (List.filter R xs)
  }}}.
Proof.
  iIntros (ϕ) "(H_isList & #H_p & HQs) H_ϕ". wp_rec. wp_pures.
  iApply (foldr_spec_PI Q
                        (fun xs' acc => is_list acc (List.filter R xs'))%I
                  with "[$H_isList HQs] [H_ϕ]").
  - iSplitR.
    + iIntros (x a' ?) "!# %ϕ'". iIntros "[HQ H_isList] H_ϕ'".
      repeat (wp_pure _). wp_bind (p x). iApply ("H_p" with "[$HQ]").
      iNext. iIntros (r) "H". iSimplifyEq. destruct (R x); wp_if.
      * wp_rec. wp_pures. wp_alloc l. wp_pures. iApply "H_ϕ'".
        iExists l, a'. by iFrame.
      * by iApply "H_ϕ'".
    + by iSplit.
  - iNext. iApply "H_ϕ".
Qed.


Lemma map_spec P Q (f hd : val) (xs : list val) :
  {{{
       is_list hd xs
        ∗ (∀ (x : val), {{{ P x }}}
                          f x
                        {{{r, RET r; Q x r}}})
        ∗ [∗ list] x ∈ xs, P x
  }}}
    map_list f hd
  {{{
       r, RET r; ∃ (ys : list val),  is_list r ys
                                     ∗ ([∗ list] p ∈ zip xs ys, Q (fst p) (snd p))
                                     ∗ ⌜List.length ys = List.length xs⌝
  }}}.
Proof.
  iIntros (ϕ) "[H_is_list [#H1 H_P_xs]] H_ϕ".
  wp_rec. wp_pures.
  iApply (foldr_spec_PI
            P
            (fun xs acc => ∃ ys,  (is_list acc ys)
                                 ∗ ([∗ list] p ∈ zip xs ys, Q (fst p) (snd p))
                                 ∗ ⌜length xs = length ys⌝)%I
            with "[H_is_list H1 H_P_xs] [H_ϕ]").
  - iSplitR "H_is_list H_P_xs".
    + iIntros (x a' ys). iModIntro. iIntros (ϕ') "(H_Px & H_Q) H_ϕ'". wp_pures.
      wp_bind (f x). iApply ("H1" with "[H_Px][H_Q H_ϕ']"); try done.
      iNext. iIntros (r) "H_Qr". wp_rec. wp_alloc l. wp_pures. iApply "H_ϕ'".
      iDestruct "H_Q" as (ys') "(H_is_list_ys' & H_Qys' & %)". iExists (r::ys').
      iSplitR "H_Qr H_Qys'".
      * unfold is_list. iExists l, a'. fold is_list. by iFrame.
      * iSimplifyEq. iFrame. eauto.
    + iFrame. iExists []. iSplit; by simpl.
  - iNext. iIntros (r) "H". iApply "H_ϕ". iDestruct "H" as "(_ & H_Q)".
    iDestruct "H_Q" as (ys) "(H_isList & H_Q & %)". iExists ys. by iFrame.
Qed.


Lemma about_length {A : Type} (xs : list A) (n : nat) :
  length xs = S n -> exists x xs', xs = x::xs'.
Proof.
  intro H. induction xs as [| x xs' ].
  - inversion H.
  - by exists x, xs'.
Qed.

Lemma inc_with_map hd (xs : list Z) :
  {{{ is_list hd (List.map (fun (n : Z) => #n) xs) }}}
    incr hd
  {{{ v, RET v; is_list v (List.map (fun (n : Z) => #n) (List.map Z.succ xs)) }}}.
Proof.
  iIntros (ϕ) "H_isList H_ϕ". wp_rec. wp_pures.
  wp_apply (map_spec
             (fun x => (∃ (n : Z), ⌜x = #n⌝)%I)
             (fun x r =>  (∃ (n' : Z),
                             ⌜r = #(Z.succ n')⌝
                                ∗ ⌜x = #n'⌝)%I)
           with "[$H_isList] [H_ϕ]").
  - iSplit.
    + iIntros (x) "!#". iIntros (ϕ') "H1 H2". wp_lam. iDestruct "H1" as (n) "H_x".
      iSimplifyEq. wp_binop. iApply "H2". by iExists n.
    + rewrite big_sepL_fmap. rewrite big_sepL_forall. eauto.
  - iNext. iIntros (r) "H". iApply "H_ϕ". iDestruct "H" as (ys) "(H_isList & H_post & H_length)".
    iAssert (⌜ys = (List.map (λ n : Z, #n) (List.map Z.succ xs))⌝)%I with "[-H_isList]" as %->.
    { iInduction ys as [| y ys'] "IH" forall (xs); iDestruct "H_length" as %H.
       - simpl. destruct xs; first by simpl. inversion H.
       - rewrite length_fmap in H. symmetry in H. simpl in H.
         destruct (about_length _ _ H) as (x & xs' & ->). simpl.
         iDestruct "H_post" as "(H_head & H_tail)".
         iDestruct "H_head" as (n') "(% & %)". iSimplifyEq.
         iDestruct ("IH" with "H_tail []") as %->.
         {  by rewrite length_fmap. }
         done.
    }
    iFrame.
Qed.

End list_spec.
