(** Concurrent bag specification from the HOCAP paper.
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

This file: abstract bag specification
*)
From iris.heap_lang Require Import proofmode notation.
From iris.base_logic.lib Require Export invariants.
From stdpp Require Import gmultiset.

Record bag Σ `{!heapGS Σ} := Bag {
  (* -- operations -- *)
  newBag : val;
  pushBag : val;
  popBag : val;
  (* -- predicates -- *)
  (* name is used to associate bag_contents with is_bag *)
  name : Type;
  is_bag (N: namespace) (γ: name) (b: val) : iProp Σ;
  bag_contents (γ: name) (X: gmultiset val) : iProp Σ;
  (* -- ghost state theory -- *)
  is_bag_persistent N γ b : Persistent (is_bag N γ b);
  bag_contents_timeless γ X : Timeless (bag_contents γ X);
  bag_contents_agree γ X Y: bag_contents γ X -∗ bag_contents γ Y -∗ ⌜X = Y⌝;
  bag_contents_update γ X X' Y:
    bag_contents γ X ∗ bag_contents γ X' ==∗
    bag_contents γ Y ∗ bag_contents γ Y;
  (* -- operation specs -- *)
  newBag_spec N :
    {{{ True }}} newBag #() {{{ x γ, RET x; is_bag N γ x ∗ bag_contents γ ∅ }}};
  pushBag_spec N P Q γ b v :
    □ (∀ (X : gmultiset val), bag_contents γ X ∗ P
                     ={⊤∖↑N}=∗ ▷ (bag_contents γ ({[+ v +]} ⊎ X) ∗ Q)) -∗
    {{{ is_bag N γ b ∗ P }}}
      pushBag b (of_val v)
    {{{ RET #(); Q }}};
  popBag_spec N P Q γ b :
    □ (∀ (X : gmultiset val) (y : val),
               bag_contents γ ({[+ y +]} ⊎ X) ∗ P
               ={⊤∖↑N}=∗ ▷ (bag_contents γ X ∗ Q (SOMEV y))) -∗
    □ (bag_contents γ ∅ ∗ P ={⊤∖↑N}=∗ ▷ (bag_contents γ ∅ ∗ Q NONEV)) -∗
    {{{ is_bag N γ b ∗ P }}}
      popBag b
    {{{ v, RET v; Q v }}};
}.

Global Arguments newBag {_ _} _.
Global Arguments popBag {_ _} _.
Global Arguments pushBag {_ _} _.
Global Arguments newBag_spec {_ _} _ _ _.
Global Arguments popBag_spec {_ _} _ _ _ _ _ _.
Global Arguments pushBag_spec {_ _} _ _ _ _ _ _ _.
Global Arguments is_bag {_ _} _ _ _ _.
Global Arguments bag_contents {_ _} _ _.
Global Arguments bag_contents_update {_ _} _ {_ _ _}.
Global Existing Instances is_bag_persistent bag_contents_timeless.

