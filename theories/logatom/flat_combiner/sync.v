(* Syncer spec *)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.

Section sync.
  Context `{!heapGS Σ} (N : namespace).

  (* TODO: We could get rid of the x, and hard-code a unit. That would
     be no loss in expressiveness, but probably more annoying to apply.
     How much more annoying? And how much to we gain in terms of things
     becoming easier to prove? *)
  Definition synced R (f f': val) :=
    (□ ∀ P Q (x: val), {{{ R ∗ P }}} f x {{{ v, RET v; R ∗ Q v }}} →
                       {{{ P }}} f' x {{{ v, RET v; Q v }}})%I.

  (* Notice that `s f` is *unconditionally safe* to execute, and only 
     when executing the returned f' we have to provide a spec for f.
     This is crucial. *)
  (* TODO: Use our usual style with a generic post-condition. *)
  Definition is_syncer (R: iProp Σ) (s: val) :=
    (□ ∀ (f : val), WP s f {{ f', synced R f f' }})%I.

  Definition mk_syncer_spec (mk_syncer: val) :=
    ∀ (R: iProp Σ),
      {{{ R }}} mk_syncer #() {{{ s, RET s; is_syncer R s }}}.
End sync.
