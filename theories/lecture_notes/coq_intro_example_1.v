(* In this file we explain how to do the "parallel increment" example (Example
   8.4) from the lecture notes in Iris in Coq. *)

(* Contains definitions of the weakest precondition assertion, and its basic
   rules. *)
From iris.program_logic Require Export weakestpre.
(* Definition of invariants and their rules (expressed using the fancy update
   modality). *)
From iris.base_logic.lib Require Export invariants.

(* Files related to the interactive proof mode. The first import includes the 
   general tactics of the proof mode. The second provides some more specialized 
   tactics particular to the instantiation of Iris to a particular programming 
   language. *)
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Import notation lang.

(* We also import the parallel composition construct. This is not a primitive of
   the language, but is instead derived. This file contains its definition, and
   the proof rule associated with it. *)
From iris.heap_lang.lib Require Import par.

(* The following line imports some Coq configuration we commonly use in Iris
   projects, mostly with the goal of catching common mistakes. *)
From iris.prelude Require Import options.

(* We define our terms. The Iris Coq library defines many notations for
   programming language constructs, e.g., lambdas, allocation, accessing and so
   on. The complete list of notations can be found in
   theories/heap_lang/notations.v file in the iris-coq repository.
   The # in the notation is used to embed literals, e.g., variables, numbers, as
   values of the programming language. *)
Definition incr (ℓ : loc) : expr := #ℓ <- !#ℓ + #1.

Section proof.
  (* In order to do the proof we need to assume certain things about the
     instantiation of Iris. In particular, even the heap is handled in an
     analogous way as other ghost state. This line states that we assume the
     Iris instantiation has sufficient structure to manipulate the heap, e.g.,
     it allows us to use the points-to predicate. *)
  Context `{!heapGS Σ}.
  (* Recall that parallel composition construct is defined in terms of fork. To
     prove the expected rules for this construct we need some particular ghost
     state in the instantiation of Iris, as explained in the lecture notes. The
     following line states that we have this ghost state. *)
  Context `{!spawnG Σ}.
  (* The variable Σ has to do with what ghost state is available, and the type
     of Iris propositions (written Prop in the lecture notes) depends on this Σ.
     But since Σ is the same throughout the development we shall define
     shorthand notation which hides it. *)
  Notation iProp := (iProp Σ).
  (* As in the paper proof we will need an invariant to share access to a
     location. This invariant will be allocated in this namespace which is a
     parameter of the whole development. *)
  Context (N : namespace).
  

  (* We now start with the details particular to the example. Everything above
     was essentially boilerplate which will be there in most verifications.  *)

  (* The invariant we are going to use is the following. Note that this is the
     body of the invariant, not the invariant assertion. Note the scope
     delimiter "%I". This is to tell Coq to parse the logical formula as an Iris
     assertion, i.e., to interpret the connectives as Iris connectives, and not
     perhaps as Coq connectives, or something else. The final piece of syntax is
     ⌜ ... ⌝. This is used to embed Coq propositions as Iris assertions. That
     is, ≥ is the ordinary greater-than-or-equal relation on natural numbers,
     and we make it an Iris assertion by using ⌜ ... ⌝. Semantically, the
     embedding is such that the embedded assertion either holds for all
     resources, or none. *)
  Definition incr_inv (ℓ : loc) (n : Z) : iProp := (∃ (m : Z), ⌜(n ≤ m)%Z⌝ ∗ ℓ ↦ #m)%I.

  (** The main proofs. *)
  (* As in example 7.5 in the notes we will show the following specification.
  The specification is  parametrized by any location ℓ and natural number n *)
  Lemma parallel_incr_spec (ℓ : loc) (n : Z):
    {{{ ℓ ↦ #n }}} (incr ℓ) ||| (incr ℓ) ;; !#ℓ {{{m, RET #m; ⌜(n ≤ m)%Z⌝ }}}.
  Proof using Type* N.
    (* We first unfold the triple notation. Recall its definition from Section 9
       of the lecture notes. *)
    iIntros (Φ) "Hpt HΦ".
    (* As in the paper proof we now allocate an invariant (in namespace N) and
       transfer the points-to predicate into it. This is achieved by using the
       rule/lemma inv_alloc. But since the allocation of invariants involves the
       fancy update modality we use the iMod tactic around the lemma. This
       tactic knows about the structural rules of the update modalities, and the
       interaction of the update modality and the weakest precondition
       assertion, and thus it automatically removes the modality as much as
       possible.

       The inv_alloc rule has three parameters. The namespace in which to
       allocate, the mask which is to be used on the fancy update modality (see
       the rule in the notes), and the body of the invariant to be allocated.
       Here we leave the mask implicit, since it is determined by the current
       goal (the weakest precondition has a mask, which, if not explicitly
       stated, is the top mask, containing all the invariant names.

       The next ingredient in the line below is the "with" construct. This tells
       the iMod tactic which of the assumptions are to be used to satisfy the
       assumptions of the inv_alloc rule/lemma. See the ProofMode.md in the
       iris-coq repository for the precise syntax of the pattern which follows
       the "with" keyword. Here we are using the simplest pattern, we are just
       going to use one of our assumptions.
       
       Finally we have the 'as "#Hinv"'. This tells the iMod tactic to name the
       conclusion of the inv_alloc rule "HInv", and add it as one of the
       persistent assumptions. The # symbol is a pattern used to denote
       persistent assumptions. When we wish to move an assertion to the
       persistent context the interactive proof mode uses Coq's typeclass search
       to try and determine whether the assertion is indeed persistent. In this
       case the assertion is an invariant, hence it is. *)
    iMod (inv_alloc N _ (incr_inv ℓ n) with "[Hpt]") as "#HInv".
    (* Now we have two subgoals. We need to prove the assumptions of the
       inv_alloc rule first. *)
    - iNext; iExists n; iFrame. 
      (* This is easy to prove. We use the next introduction rule (the tactic
         iNext). And then we have to prove that ℓ ↦ #n ⊢ ∃ m, ℓ ↦ #m ∗ m ≥ n. We
         pick n as the witness of the existential, and then we have to prove ℓ ↦
         #n ⊢ ℓ ↦ #n ∗ n ≥ n. We do this by first "framing" away the ℓ ↦ #n. The
         iFrame tactic is essentially the rule ∗-mono.

         After these we are left with the goal ⌜n ≥ n⌝. To prove such goals we,
         most of the time, wish to exit the interactive proof mode and go to the
         ordinary Coq proof mode. This is achieved via the iIntros "!%" tactic.
         Here, "!%" is another pattern, as described in ProofMode.md. Hence,
         after this we are left with proving n ≥ n, which is solved by the lia
         tactic (linear integer arithmetic solver). *)
      iIntros "!%". lia.
    - (* Next we use wp_bind rule, as in the paper proof. This rule is
         implemented by the wp_bind tactic, which does some bookkeeping so that
         the bind rule is as easy to use as on paper. The argument to the tactic
         is the expression we wish to focus on. In this case the first part of
         the sequencing expression. Note the scope delimiter %E. This is the
         scope delimiter for expressions of the language with which Iris is
         instantiated. *)
      wp_bind (incr ℓ ||| incr ℓ )%E.
      (* Now we are in a position to use the parallel composition rule, which is
         proved in the par library we have imported above. The rule/lemma is
         called wp_par. The two arguments are the conclusions of the two
         parallel threads. Here they are simply True, as in the paper proof when
         we used the ht-par rule.
         The term needs a bit of reduction to fit the [wp_par] lemma, so we use
         [wp_smart_apply].*)
      wp_smart_apply (wp_par (λ _ , ⌜True⌝)%I (λ _ , ⌜True⌝)%I).
      (* We now have three subgoals. The first two are proofs that each thread
      does the correct thing, and the final goal is to show that the combined
      conclusion of the two threads implies the desired conclusion. This last
      part is a peculiarity of the wp_par rule as stated in Coq. It builds in
      the rule of consequence, which we would otherwise have to use manually, as
      we did when proving on paper. *)
      + (* The proof that the first thread is correct is exactly the same as the
           proof on paper. The expression is not atomic, so we cannot open the
           invariant immediately. Thus we do as usual, we use the bind rule to
           reshape it, then open the invariant and then ... There is a minor
           technicality we need to do first. We need to unfold the definition of incr.*)
        rewrite /incr.
        wp_bind (!#ℓ)%E.
        (* Now we can open the invariant to read a value stored at location ℓ. *)
        (* Opening invariants is done using the iInv tactic. In the most basic
           form it takes a namespace as the first argument, and two named
           assertions. These are the two parts of the inv_open rule (the two
           parts of the conclusion). *)
        iInv N as "H" "Hclose".
        (* After this we can read the value, since we have the resources. The
           tactic wp_load implements the rule for reading a memory location. But
           first, we need to eliminate the existential "H" (the incr_inv
           assertion) to get a points-to predicate. This we do using the
           iDestruct tactic. The pattern this time is quite advanced. The
           assertion named H is ▷∃ m, ⌜m ≥ n⌝ ∗ ℓ ↦ m. The assertion ∃m, ⌜m ≥ n⌝
           ∗ ℓ ↦ m is timeless. Hence because the conclusion is the weakest
           precondition assertion we can remove the later, which is the purpose
           of > in the beginning of the pattern. The rest of the pattern is (m)
           and [% Hpt]. The (m) states to name the variable we get after
           destructing the existential, m. Finally we have to deal with ⌜m ≥ n⌝
           ∗ ℓ ↦ m. The pattern [% Hpt] states to move the first part, ⌜m ≥ n⌝
           to the pure Coq context (the % character), and it states that the
           second part should be named Hpt. *)
        iDestruct "H" as (m) ">[% Hpt]".
        (* Now we have a points-to assertion in context, so we can use wp_load rule. *)
        wp_load.
        (* After reading we must again close the invariant. For this we have the
           "Hclose" assertion, which we got when opening the invariant.
           We close the invariant by transferring the points-to predicate back.
           And since closing involves manipulation of fancy updates we use the
           iMod tactic. The as "_" pattern states to ignore the conclusion of
           "Hclose" assertion. The interesting part of Hclose is the change of
           masks, and the conclusion is simply True, which we can ignore. *)
        iMod ("Hclose" with "[Hpt]") as "_".
        { iNext; iExists m; iFrame; iIntros "!%"; auto. }
        (* We now have to prove |={T}=> wp ... , but the modality is just in the
           way. Thus we use the introduction rule to get rid of it in the goal.
           iModIntro is the tactic which introduces modalities such as the update
           and the fancy update modality. *)
        iModIntro.
        (* Next we do as on paper. We compute the value #m + #1 into #(m+1),
           which is simple to do with wp_bind and wp_op tactics. In fact, wp_op
           on its own would suffice, since it tries to find a basic operation
           and use wp_bind automatically if it does.*)
        wp_bind (_ + _)%E ; wp_op.
        (* We then repeat the process of opening the invariant, writing, and
        closing the invariant. But to illustrate the flexibility of tactics we
        join the call to iInv and iDestruct into one, with a complex pattern. *)
        iInv N as (k) ">[% Hpt]" "Hclose".
        wp_store.
        iMod ("Hclose" with "[Hpt]") as "_".
        { iNext; iExists (m+1)%Z; iFrame; iIntros "!%"; lia. }
        (* And we are left with proving |={T}=> True, which is trivial. *)
        done.
      + (* The second thread is exactly the same as the first, so the proof is
           the same. We could have factored out the proof into a separate lemma,
           but instead we here give a shorter version using more advanced
           features of the tactics. The reader should compare it with the
           previous proof. *)
        rewrite /incr.
        wp_bind (!#ℓ)%E.
        iInv N as (m) ">[% Hpt]" "Hclose".
        wp_load.
        iMod ("Hclose" with "[Hpt]") as "_".
        { iExists m; iFrame; done. }
        iModIntro.
        wp_op.
        iInv N as (k) ">[% Hpt]" "Hclose".
        wp_store.
        iMod ("Hclose" with "[Hpt]") as "_"; last done.
        { iExists (m+1)%Z; iFrame; iIntros "!%"; lia. }
      + (* And the last goal is before us. We first simplify to get rid of
           superflous assumptions and variables. As above, the pattern _ means
           ignore this assumption. It is always safe to ignore True as an
           assumption. The iIntros tactic can additionally be used to introduce
           the forall quantifiers by giving variable names as the first
           argument. Here we do not care about the variable names so we give ?
           as the pattern, which lets Coq generate a variable name for us. *)
        iIntros (? ?) "_".
        (* To be able to use the wp_tactics the goal needs to be of the form WP
           ..., thus we first remove the later modality using the later
           introduction rule, implemented by the iNext tactic. After that we
           have to deal with the application of a function with a dummy argument,
           i.e., sequencing. The wp_seq tactic handles it. *)
        iNext.
        wp_seq.
        (* The last interesting part of the proof is before us. We do exactly as
           we did on paper. We open the invariant, and read the value. And the
           invariant will tell us that the value is at least n. We can then apply
           the "continuation" HΦ to conclude the proof. *) 
        iInv N as (m) ">[% Hpt]" "Hclose".
        wp_load.
        iMod ("Hclose" with "[Hpt]") as "_".
        { iExists m; iFrame; done. }
        iModIntro.
        (* As stated above, to conclude the proof we apply the "continuation"
           HΦ. This illustrates another new feature of the tactics. Observe that
           HΦ is a universally quantified formula. To instantiate the variables
           we use the $! notation as follows. *)
        iApply ("HΦ" $! m).
        (* And we are left with proving the premise of the continuation, which
           is easy, since it is one of our assumptions which we obtained when
           opening the invariant. *)
        done.
  Qed.
End proof.
