From iris.heap_lang Require Import proofmode notation.

(** Specification for an eager coin. The coin is only ever tossed once, at the
time of its creation with [new_coin]. All subsequent calls to [read_coin] give
the same value. *)
Record eager_coin_spec `{!heapGS Σ} := EagerCoinSpec {
  (* -- operations -- *)
  new_coin: val;
  read_coin: val;
  (* -- predicates -- *)
  coin (c : val) (b : bool) : iProp Σ;
  (* -- predicate properties -- *)
  coin_exclusive c b1 b2 : coin c b1 -∗ coin c b2 -∗ False;
  (* -- operation specs -- *)
  new_coin_spec :
    {{{ True }}}
        new_coin #()
    {{{ c b, RET c ; coin c b  }}};
  read_coin_spec c b :
    {{{ coin c b }}}
        read_coin c
    {{{ RET #b ; coin c b }}};
}.
Global Arguments eager_coin_spec _ {_}.
