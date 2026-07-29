From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.

(** Specifying snapshots with histories
    Implementing atomic pair snapshot data structure from Sergey et al. (ESOP 2015) *)

Record atomic_snapshot {Σ} `{!heapGS Σ} := AtomicSnapshot {
    new_snapshot : val;
    read : val;
    write : val;
    read_with : val;
    (* other data *)
    name: Type;
    name_eqdec : EqDecision name;
    name_countable : Countable name;
    (* predicates *)
    is_snapshot (N : namespace) (γ : name) (p : val) : iProp Σ;
    snapshot_content (γ : name) (a: val) : iProp Σ;
    (* predicate properties *)
    is_snapshot_persistent N γ p : Persistent (is_snapshot N γ p);
    snapshot_content_timeless γ a : Timeless (snapshot_content γ a);
    snapshot_content_exclusive γ a1 a2 :
      snapshot_content γ a1 -∗ snapshot_content γ a2 -∗ False;
    (* specs *)
    new_snapshot_spec N (v : val) :
      {{{ True }}} new_snapshot v {{{ γ p, RET p; is_snapshot N γ p ∗ snapshot_content γ v }}};
    read_spec N γ p :
      is_snapshot N γ p -∗
      <<{ ∀∀ v : val, snapshot_content γ v  }>>
        read p @ ↑N
      <<{ snapshot_content γ v | RET v }>>;
    write_spec N γ (v: val) p :
      is_snapshot N γ p -∗
      <<{ ∀∀ w : val, snapshot_content γ w  }>>
        write p v @ ↑N
      <<{ snapshot_content γ v | RET #() }>>;
    read_with_spec N γ p (l : loc) :
      is_snapshot N γ p -∗
      <<{ ∀∀ v w : val, snapshot_content γ v ∗ l ↦ w }>>
        read_with p #l @ ↑N
      <<{ snapshot_content γ v ∗ l ↦ w | RET (v, w) }>>;
}.
Global Arguments atomic_snapshot _ {_}.

Global Existing Instances
  is_snapshot_persistent snapshot_content_timeless
  name_countable name_eqdec.
