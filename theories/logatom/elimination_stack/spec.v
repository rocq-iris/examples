From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import atomic_heap.

(** A general logically atomic interface for a stack. *)
Record atomic_stack {Σ} `{!heapGS Σ, !atomic_heap, !atomic_heapGS Σ} := AtomicStack {
  (* -- operations -- *)
  new_stack : val;
  push : val;
  pop : val;
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_stack (N : namespace) (γs : name) (v : val) : iProp Σ;
  stack_content (γs : name) (l : list val) : iProp Σ;
  (* -- predicate properties -- *)
  is_stack_persistent N γs v : Persistent (is_stack N γs v);
  stack_content_timeless γs l : Timeless (stack_content γs l);
  stack_content_exclusive γs l1 l2 :
    stack_content γs l1 -∗ stack_content γs l2 -∗ False;
  (* -- operation specs -- *)
  new_stack_spec N :
    N ## atomic_heapN →
    heap_inv -∗
    {{{ True }}} new_stack #() {{{ γs s, RET s; is_stack N γs s ∗ stack_content γs [] }}};
  push_spec N  γs s (v : val) :
    is_stack N γs s -∗
    <<{ ∀∀ l : list val, stack_content γs l }>>
      push s v @ (↑N ∪ ↑atomic_heapN)
    <<{ stack_content γs (v::l) | RET #() }>>;
  pop_spec N γs s :
    is_stack N γs s -∗
    <<{ ∀∀ l : list val, stack_content γs l }>>
      pop s @ (↑N ∪ ↑atomic_heapN)
    <<{ stack_content γs (tail l)
      | RET match l with [] => NONEV | v :: _ => SOMEV v end }>>;
}.
Global Arguments atomic_stack _ {_ _ _}.

Global Existing Instances
  is_stack_persistent stack_content_timeless
  name_countable name_eqdec.
