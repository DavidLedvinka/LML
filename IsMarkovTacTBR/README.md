# To be reviewed later

Two earlier attempts at the proof API for `rdo` programs, kept for reference. Neither is imported
by `LeanMachineLearning.lean`, so neither is compiled by the build. Both define `RDo.IsMarkov`, so
they cannot coexist with each other nor with `LeanMachineLearning/RDo/Tactic/`.

## `Full/`

The complete API, closed under every construct an `rdo` block can produce.

* `Probability.lean` — `IsMarkov` with all its closure properties (`mBind`, `mPure`, `mMap`,
  `ite`, `for` over `List`/`Array`/`Vector`, `for h : a in xs`, early `return`, and loops whose
  collection depends on the parameter), the classes `IsMarkovForIn'`/`IsMarkovForIn`, the
  loop-unrolling equations, and an `is_markov` tactic written as a `macro` chaining `first`
  alternatives.
* `Measurable.lean` — measurability of the types an `rdo` program manipulates: `ForInStep`,
  `Option`, sigma types, `List` and `Array` (including `List.cons` and `Array.push`).
* `ProbabilityExamples.lean` — about fifteen programs, all proved by `is_markov`.

## `Minimal/`

The same approach cut down to what proves two specific goals, one idea per file: `IsMarkov.lean`,
`Bind.lean`, `ForInStep.lean`, `ForInList.lean`, `Tactic.lean` (a pruned version of the same
`macro`-based tactic), `ProbabilityExamples.lean`.

## What replaced them

`LeanMachineLearning/RDo/Tactic/` starts over with a tactic written in Lean metaprogramming
instead of a `macro`: it inspects the program, picks the lemma itself, recurses, and hands the
measurability side conditions back as goals.
