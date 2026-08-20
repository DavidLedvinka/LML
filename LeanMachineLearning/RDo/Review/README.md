# To be reviewed later

This directory holds a first, complete version of the proof API for `rdo` programs:

* `Probability.lean` — the `IsMarkov` predicate together with all its closure properties
  (`mBind`, `mPure`, `mMap`, `ite`, `for` over `List`/`Array`/`Vector`, `for h : a in xs`, early
  `return`, and loops whose collection depends on the parameter), the classes
  `IsMarkovForIn'`/`IsMarkovForIn`, the loop-unrolling equations, and a fuller `is_markov` tactic than the one of the parent
  directory (one rule per closure property above).
* `Measurable.lean` — measurability of the types an `rdo` program manipulates: `ForInStep`,
  `Option`, sigma types, `List` and `Array` (including `List.cons` and `Array.push`).
* `ProbabilityExamples.lean` — about fifteen programs, all proved by `is_markov`.

These files are **not** imported by `LeanMachineLearning.lean` and are therefore not compiled by
the build. They redefine `RDo.IsMarkov`, so they cannot coexist with the files of the parent
directory as long as the latter exist.

The parent directory holds only what the two proofs of
`LeanMachineLearning/RDo/ProbabilityExamples.lean` strictly need.
