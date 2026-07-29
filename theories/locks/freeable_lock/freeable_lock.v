From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import primitive_laws notation.

(** A general interface for a lock.
All parameters are implicit, since it is expected that there is only one
[heapGS_gen] in scope that could possibly apply. *)
Structure freeable_lock `{!heapGS_gen hlc Σ} := Lock {
  (** * Operations *)
  newlock : val;
  acquire : val;
  release : val;
  freelock : val;
  (** * Predicates *)
  (** [name] is used to associate locked with [is_lock] *)
  name : Type;
  (** No namespace [N] parameter because we only expose program specs, which
  anyway have the full mask. *)
  is_lock (γ: name) (lock: val) (R: iProp Σ) : iProp Σ;
  own_lock (γ: name) (q: frac) : iProp Σ;
  locked (γ: name) : iProp Σ;
  (** * General properties of the predicates *)
  is_lock_ne γ lk : Contractive (is_lock γ lk);
  is_lock_persistent γ lk R : Persistent (is_lock γ lk R);
  is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ↔ R2) -∗ is_lock γ lk R2;
  own_lock_timeless γ q : Timeless (own_lock γ q);
  own_lock_split γ q1 q2 :
    own_lock γ (q1+q2) ⊣⊢ own_lock γ q1 ∗ own_lock γ q2;
  own_lock_valid γ q :
    own_lock γ q -∗ ⌜q ≤ 1⌝%Qp;
  locked_timeless γ : Timeless (locked γ);
  locked_exclusive γ : locked γ -∗ locked γ -∗ False;
  (** * Program specs *)
  newlock_spec (R : iProp Σ) :
    {{{ True }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R ∗ locked γ ∗ own_lock γ 1 }}};
  acquire_spec γ lk q R :
    {{{ is_lock γ lk R ∗ own_lock γ q }}} acquire lk {{{ RET #(); locked γ ∗ own_lock γ q ∗ R }}};
  release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}};
  freelock_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ own_lock γ 1 }}} freelock lk {{{ RET #(); True }}};
}.
Global Hint Mode freeable_lock + + + : typeclass_instances.

Global Existing Instances is_lock_ne is_lock_persistent own_lock_timeless locked_timeless.

Global Instance is_lock_proper hlc Σ `{!heapGS_gen hlc Σ} (L : freeable_lock) γ lk :
  Proper ((≡) ==> (≡)) (L.(is_lock) γ lk) := ne_proper _.

Section freeable_lock.
  Context `{!heapGS Σ} (l : freeable_lock).

  Lemma own_lock_halves γ q :
    l.(own_lock) γ q ⊣⊢ l.(own_lock) γ (q/2) ∗ l.(own_lock) γ (q/2).
  Proof. rewrite -own_lock_split Qp.div_2 //. Qed.
End freeable_lock.
