# IRIS EXAMPLES

Some example verification demonstrating the use of Iris.

## Prerequisites

This version is known to compile with:

 - Rocq 9.1.0
 - A development version of [Iris](https://gitlab.mpi-sws.org/iris/iris)
 - A development version of [Autosubst](https://github.com/coq-community/autosubst)

## Building from source

When building from source, we recommend to use opam (2.0.0 or newer) for
installing the dependencies.  This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update, do `git pull`.  After an update, the development may fail to compile
because of outdated dependencies.  To fix that, please run `opam update`
followed by `make build-dep`.

## Case Studies

This repository contains the following case studies:

* [barrier](theories/barrier): Implementation and proof of a barrier as
  described in ["Higher-Order Ghost State"](http://doi.acm.org/10.1145/2818638).
* [cl_logic](theories/cl_logic): An embedding of classical logic into Coq using
  the Gödel-Gentzen translation. It defines `clProp` as the subset of Coq
  propositions that are stable under double negation. The logic `clProp` is a
  BI, so the proof mode can be used to carry out proofs in classical logic,
  without axioms.
* [logrel](theories/logrel): Logical relations.
  - [logrel/stlc](theories/logrel/stlc): A unary logical relation for semantic
    typing STLC (simply-typed lambda calculus) with De Bruijn indices (using
    Autosubst).
  - [logrel/F_mu_ref_conc](theories/logrel/F_mu_ref_conc): The logical relations
    for F_mu_ref_conc (System F with recursive types, references and concurrency)
    with De Bruijn indices (using Autosubst) from the
    [IPM paper](http://doi.acm.org/10.1145/3093333.3009855):
    + Unary logical relations proving type safety.
    + Binary logical relations for proving contextual refinements.
    + Proof of refinement for a pair of fine-grained/coarse-grained
      concurrent counter implementations.
    + Proof of refinement for a pair of fine-grained/coarse-grained
      concurrent stack implementations.
  - If you are looking for a well-explained logical relation for Iris's HeapLang,
    take a look at our [POPL20 tutorial](https://gitlab.mpi-sws.org/iris/tutorial-popl20/).
* [logatom](theories/logatom): Proofs of various logically atomic specifications:
  - Elimination Stack (by Ralf Jung).
  - Conditional increment (inspired by [this paper](https://people.mpi-sws.org/~dreyer/papers/relcon/paper.pdf))
    and RDCSS (as in [this paper](https://timharris.uk/papers/2002-disc.pdf))
    (by Marianna Rapoport, Rodolphe Lepigre and Gaurav Parthasarathy).
  - [Herlihy-Wing-Queue](https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf)
    (by Rodolphe Lepigre).
  - Atomic Snapshot (by Marianna Rapoport).
  - Treiber Stack (by Zhen Zhang, and another version by Rodolphe Lepigre).
  - Flat Combiner (by Zhen Zhang, also see
    [this archived documentation](https://gitlab.mpi-sws.org/FP/iris-atomic/tree/master/docs)).
  - Counter with a backup, the case study from Section 4 of the
    [later credits paper](https://plv.mpi-sws.org/later-credits/) (by Simon
    Spies).
* [spanning_tree](theories/spanning_tree): Proof of a concurrent spanning tree
  algorithm (by Amin Timany).
* [concurrent_stacks](theories/concurrent_stacks): Proof of an implementation of
  concurrent stacks with helping by Daniel Gratzer et. al., as described in the
  [report](http://iris-project.org/pdfs/2017-case-study-concurrent-stacks-with-helping.pdf).
* [lecture_notes](theories/lecture_notes): Coq examples for the
  [Iris lecture notes](http://iris-project.org/tutorial-material.html).
* [hocap](theories/hocap): Formalizations of the concurrent bag and concurrent
  runners libraries from the [HOCAP paper](https://dl.acm.org/citation.cfm?id=2450283)
  (by Dan Frumin). See the associated [README](theories/hocap/README.md).
* [locks](theories/locks): Various proofs around locks.
  - [array_based_queuing_lock](/theories/locks/array_based_queuing_lock): Proof
    of safety of an implementation of the array-based queuing lock. This example
    is also covered in the chapter
    ["Case study: The Array-Based Queueing Lock"](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf#section.10)
    in the Iris lecture notes.

## For Developers: How to update the Iris dependency

* Do the change in Iris, push it.
* Wait for CI to publish a new Iris version on the opam archive, then run
  `opam update iris-dev`.
* In iris-examples, change the `opam` file to depend on the new version.
  (In case you do not use opam yourself, you can see recently published versions
  [in this repository](https://gitlab.mpi-sws.org/iris/opam/commits/master).)
* Run `make build-dep` (in iris-examples) to install the new version of Iris.
  You may have to do `make clean` as Coq will likely complain about .vo file
  mismatches.
