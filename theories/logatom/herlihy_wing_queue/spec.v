From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** A general logically atomic interface for Herlihy-Wing queues. *)
Record atomic_hwq {Σ} `{!heapGS Σ} := AtomicHWQ {
  (* -- operations -- *)
  new_queue : val;
  enqueue : val;
  dequeue : val;
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_hwq (N : namespace) (sz : nat) (γ : name) (v : val) : iProp Σ;
  hwq_content (γ : name) (ls : list loc) : iProp Σ;
  (* -- predicate properties -- *)
  is_hwq_persistent N sz γ v : Persistent (is_hwq N sz γ v);
  hwq_content_timeless γ ls : Timeless (hwq_content γ ls);
  hwq_content_exclusive γ ls1 ls2 :
    hwq_content γ ls1 -∗ hwq_content γ ls2 -∗ False;
  (* -- operation specs -- *)
  new_queue_spec N (sz : nat) :
    0 < sz →
    {{{ True }}}
      new_queue #sz
    {{{ v γ, RET v; is_hwq N sz γ v ∗ hwq_content γ [] }}};
  enqueue_spec N (sz : nat) (γ : name) (q : val) (l : loc) :
    is_hwq N sz γ q -∗
    <<{ ∀∀ (ls : list loc), hwq_content γ ls }>>
      enqueue q #l @ ↑N
    <<{ hwq_content γ (ls ++ [l]) | RET #() }>>;
  dequeue_spec N (sz : nat) (γ : name) (q : val) :
    is_hwq N sz γ q -∗
    <<{ ∀∀ (ls : list loc), hwq_content γ ls }>>
      dequeue q @ ↑N
    <<{ ∃∃ (l : loc) ls', ⌜ls = l :: ls'⌝ ∗ hwq_content γ ls' | RET #l }>>;
}.
Global Arguments atomic_hwq _ {_}.

Global Existing Instances is_hwq_persistent hwq_content_timeless.
