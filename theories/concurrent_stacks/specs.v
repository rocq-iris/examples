From stdpp Require Import namespaces.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export proofmode notation.

(** General (CAP-style) spec for a concurrent bag ("per-element spec") *)
Record concurrent_bag {Σ} `{!heapGS Σ} := ConcurrentBag {
  is_bag (P : val → iProp Σ) (s : val) : iProp Σ;
  bag_pers (P : val → iProp Σ) (s : val) : Persistent (is_bag P s);
  new_bag : val;
  bag_push : val;
  bag_pop : val;
  mk_bag_spec (P : val → iProp Σ) :
    {{{ True }}}
      new_bag #()
    {{{ s, RET s; is_bag P s }}};
  bag_push_spec (P : val → iProp Σ) s v :
    {{{ is_bag P s ∗ P v }}} bag_push s v {{{ RET #(); True }}};
  bag_pop_spec (P : val → iProp Σ) s :
    {{{ is_bag P s }}} bag_pop s {{{ ov, RET ov; ⌜ov = NONEV⌝ ∨ ∃ v, ⌜ov = SOMEV v⌝ ∗ P v }}}
}.
Global Arguments concurrent_bag _ {_}.

(** General (HoCAP-style) spec for a concurrent stack *)

Record concurrent_stack {Σ} `{!heapGS Σ} := ConcurrentStack {
  is_stack (N : namespace) (P : list val → iProp Σ) (s : val) : iProp Σ;
  stack_pers (N : namespace) (P : list val → iProp Σ) (s : val) : Persistent (is_stack N P s);
  new_stack : val;
  stack_push : val;
  stack_pop : val;
  new_stack_spec (N : namespace) (P : list val → iProp Σ) :
    {{{ P [] }}} new_stack #() {{{ v, RET v; is_stack N P v }}};
  stack_push_spec (N : namespace) (P : list val → iProp Σ) (Ψ : val → iProp Σ) s v :
    {{{ is_stack N P s ∗ ∀ xs, P xs ={⊤ ∖ ↑ N}=∗ P (v :: xs) ∗ Ψ #()}}}
      stack_push s v
    {{{ RET #(); Ψ #() }}};
  stack_pop_spec (N : namespace) (P : list val → iProp Σ) Ψ s :
    {{{ is_stack N P s ∗
        (∀ v xs, P (v :: xs) ={⊤ ∖ ↑ N}=∗ P xs ∗ Ψ (SOMEV v)) ∧
        (P [] ={⊤ ∖ ↑ N}=∗ P [] ∗ Ψ NONEV) }}}
      stack_pop s
    {{{ v, RET v; Ψ v }}};
}.
Global Arguments concurrent_stack _ {_}.
