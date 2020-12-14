# Generalized Refocusing

This is the Coq formalization that accompanies the papers [Generalized
Refocusing: from Hybrid Strategies to Abstract
Machines](http://drops.dagstuhl.de/opus/volltexte/2017/7718/) and
[Deriving an Abstract Machine for Strong Call by
Need](http://drops.dagstuhl.de/opus/volltexte/2019/10515). The code
was tested under Coq version 8.11.1

The repository contains several examples in the [examples](examples/)
directory.

* The simplest is [addition](examples/addition.v).

* The most standard are  [call by name](examples/cbn_lam.v) and [call by
  value](examples/cbv_lam.v) strategies. Both these strategies are
  uniform; the examples contain comments and are meant to illustrate
  the refocusing idea.

* A relatively simple but instructive example is [lambda calculus with
  strictness operator](examples/cbn_strict.v), see Fig. 7 and 8 in the
  first paper. It contains a simple hybrid strategy and illustrates the idea
  of generalized refocusing.

* A machine with an environment for full ᵦ-normalization derived from
  a language with explicit substitutions is [here](lam_cl_es_no.v)

* [Weak call-by-need](examples/weak_cbnd.v)

* [Strong call by need](examples/strong_cbnd.v) is the most
  complicated of our examples. It is the development supporting the
  second paper.

In three cases: [MiniML](examples/miniml.v), lambda calculus with the
[normal-order](examples/lam_no.v) strategy, and lambda calculus with
the [normal-order strategy and simple explicit
substitutions](examples/lam_ses_no.v) the examples also contain a
manually defined machine and a proof of equivalence between this
machine and the automatically generated one.
