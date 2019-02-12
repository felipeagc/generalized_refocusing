# Generalized Refocusing

This is the Coq formalization that accompanies the paper [Generalized
Refocusing: from Hybrid Strategies to Abstract Machines]
(http://drops.dagstuhl.de/opus/volltexte/2017/7718/). The code was
tested under Coq version 8.7.2

The repository contains several examples in the [examples] (examples/)
directory. The simplest (about 300--400 lines of definitions and
proofs) are [call by name] (examples/cbn_lam.v) and [call by
value](examples/cbv_lam.v) strategies. Both these strategies are
uniform; the examples are meant to illustrate the refocusing idea. A
relatively simple (about 540 lines) but instructive example is [lambda
calculus with strictness operator](examples/cbn_strict.v), see Fig. 7
and 8 in the paper, with a simple hybrid strategy; it illustrates the
idea of generalized refocusing. The [weak
call-by-need](examples/weak_cbnd.v) example is about the same
size. [Strong call by need](examples/strong_cbnd.v) with about 2300
lines of definitions and proofs, is definitely the most complicated of
our examples.
