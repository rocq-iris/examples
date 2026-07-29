From iris.heap_lang Require Import proofmode notation.

(** Specification for a clairvoyant coin. A clairvoyant coin predicts all the
values that it will *non-deterministically* choose throughout the execution of
the program. This can be seen in the spec. The predicate [coin c bs] expresses
that [bs] is the list of all the values of the coin in the future. Note that
the [read_coin] operation returns the head of [bs] and that the [toss_coin]
operation takes the [tail] of [bs]. *)
Record clairvoyant_coin_spec `{!heapGS Σ} := ClairvoyantCoinSpec {
  (* -- operations -- *)
  new_coin: val;
  read_coin: val;
  toss_coin: val;
  (* -- predicates -- *)
  coin (c : val) (bs : list bool) : iProp Σ;
  (* -- predicate properties -- *)
  coin_exclusive c b1 b2 : coin c b1 -∗ coin c b2 -∗ False;
  (* -- operation specs -- *)
  new_coin_spec :
    {{{ True }}}
        new_coin #()
    {{{ c bs, RET c ; coin c bs  }}};
  read_coin_spec c bs:
    {{{ coin c bs }}}
        read_coin c
    {{{ b bs', RET #b ; ⌜bs = b :: bs'⌝ ∗ coin c bs }}};
  toss_coin_spec c bs:
    {{{ coin c bs }}}
        toss_coin c
    {{{ b bs', RET #(); ⌜bs = b :: bs'⌝ ∗ coin c bs' }}};
}.
Global Arguments clairvoyant_coin_spec _ {_}.
