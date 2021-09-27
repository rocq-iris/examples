(* In this file we explain how to do the "list examples" from the Chapter on
   Separation Logic for Sequential Programs in the Iris Lecture Notes, but where
   we use the guarded fixed point and Löb induction to define and work with the
   isList predicate. *)

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
From iris.prelude Require Import options.

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
Notation iProp := (iPropO Σ).
  
(* First we define the is_list representation predicate via a guarded fixed
   point of the functional is_list_pre. Note the use of the later modality. The
   arrows -d> express that the arrow is an arrow in the category of COFE's,
   i.e., it is a non-expansive function. To fully understand the meaning of this
   it is necessary to understand the model of Iris.

   Since the type val is discrete the non-expansiveness condition is trivially
   satisfied in this case, and we might as well have used the ordinary arrow,
   but in more complex examples the domain of the predicate we are defining will
   not be a discrete type, and the condition will be meaningful and necessary.
*)
  Definition is_list_pre (Φ : val -d> list val -d> iProp): val -d> list val -d> iProp := λ hd xs,
    match xs with
      [] => ⌜hd = NONEV⌝
    | (x::xs) => (∃ (ℓ : loc) (hd' : val), ⌜hd = SOMEV #ℓ⌝ ∗ ℓ ↦ (x,hd') ∗ ▷ Φ hd' xs)
    end%I.

  (* To construct the fixed point we need to show that the functional we have defined is contractive.
     Most of the proof is automated via the f_contractive tactic. *)
  Local Instance is_list_pre_contractive: Contractive is_list_pre.
  Proof.
    rewrite /is_list_pre. 
    intros n Φ Φ' Hdist hd ℓ.
    repeat (f_contractive || f_equiv); apply Hdist.
  Qed.

  
  Definition is_list_def: val → list val → iProp := fixpoint is_list_pre.
  Definition is_list_aux: seal (@is_list_def). Proof. by eexists. Qed.
  Definition is_list := unseal (@is_list_aux).
  Definition is_list_eq : @is_list = @is_list_def := seal_eq is_list_aux.

  Lemma is_list_unfold hd xs: is_list hd xs ⊣⊢ is_list_pre is_list hd xs.
  Proof. rewrite is_list_eq. apply (fixpoint_unfold is_list_pre). Qed.

  (* Exercise.
     Using an approach as above, given a predicate Ψ : val → iProp, define a
     predicate is_list_Ψ : val → iProp, where is_list_Ψ hd means that hd points to a linked list of elements, all of which satisfy Ψ.
   *)

  (* Exercise. Reprove all the specifications from lists.v using the above definition of is_list. *)
End list_model.
