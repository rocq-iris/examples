From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** * A general logically atomic interface for an atomic counter. *)
Record atomic_counter {Σ} `{!heapGS Σ} := AtomicCounter {
  (* -- operations -- *)
  new_counter : val;
  increment : val;
  get : val;
  get_backup : val;
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_counter (N : namespace) (γs : name) (v : val) : iProp Σ;
  value (γs : name) (n : nat) : iProp Σ;
  (* -- predicate properties -- *)
  is_counter_persistent N γs c : Persistent (is_counter N γs c);
  value_timeless γs n : Timeless (value γs n);
  value_exclusive γs n1 n2 :
    value γs n1 -∗ value γs n2 -∗ False;
  (* -- operation specs -- *)
  new_counter_spec N :
    {{{ True }}} new_counter #() {{{ c γs, RET c; is_counter N γs c ∗ value γs 0 }}};
  (* the following specs are logically atomic, using logically-atomic triples <<{ x. P }>> e <<{ y. Q }>> *)
  (* note that the [RET] clause _specifies_ that the return value is [n], and hence we do not need to introduce a separate binder [m] as is done in the formulation shown in the paper *)
  increment_spec N γs c :
    is_counter N γs c -∗
    <<{ ∀∀ n: nat, value γs n }>>
      increment c @ ↑N
    <<{ value γs (n + 1) | RET #n }>>;
  get_spec N γs c :
    is_counter N γs c -∗
    <<{ ∀∀ n: nat, value γs n }>>
      get c @ ↑N
    <<{ value γs n | RET #n }>>;
  get_backup_spec N γs c :
    is_counter N γs c -∗
    <<{ ∀∀ n: nat, value γs n }>>
      get_backup c @ ↑N
    <<{ value γs n | RET #n }>>;
}.
Global Arguments atomic_counter _ {_}.
