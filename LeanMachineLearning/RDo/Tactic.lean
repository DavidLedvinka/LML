/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.ForInList

/-!
# The `is_markov` tactic

The lemmas of the previous files are applied in a fixed order: an `rdo` program is a `mBind` of a
`mPure`, of a `for` loop or of another `mBind`, and each of them has exactly one lemma. The tactic
below just chains them, and hands the measurability side conditions to `fun_prop`.

It is deliberately restricted to the constructs the current API covers, namely `return`,
`let x ← _`, and `for a in xs` over a fixed list. A goal about any other construct is left
untouched rather than mangled.

## Two precautions worth knowing about

The rules are applied `with_reducible`. At full transparency both `Measure.bind` and
`Measure.dirac` unfold, so trying `IsMarkov.mBind` on a `return` goal (or the converse) sends the
unifier into a heartbeat timeout instead of failing; reducible transparency keeps the two head
symbols apart and makes those failures instant.

Every alternative must either close the goal or change it. `change Measurable _` would succeed
without changing anything on a goal that is already in that form, which makes `repeat'` spin;
`unfold autoParam` is used instead, since it fails when there is no `autoParam` to remove.
-/

@[expose] public section

namespace RDo

/--
`is_markov` proves that an `rdo` program in the `MeasureTheory.Measure` monad is a probability
measure (goal `IsProbabilityMeasure μ`) or a Markov kernel (goal `RDo.IsMarkov κ`).

It follows the structure of the program — `return`, `let x ← _`, and `for a in xs` over a fixed
list — and discharges the measurability side conditions with `fun_prop`. Facts `IsMarkov κ` about
the kernels the program is built from are taken from the local context or from instance search,
possibly up to a measurable reparametrisation.

Typical use, on a program defined by `def prog : Measure α := rdo ...`:
```
example : IsProbabilityMeasure prog := by unfold prog; is_markov
```

When a measurability side condition is out of reach of `fun_prop`, the tactic stops and leaves
precisely that goal, to be proved by hand.
-/
syntax (name := isMarkovTac) "is_markov" : tactic

macro_rules
  | `(tactic| is_markov) => `(tactic|
      repeat' first
        | assumption
        | infer_instance
        | fun_prop
        | (unfold autoParam; fun_prop)
        | unfold autoParam
        | (with_reducible apply RDo.IsMarkov.mPure_comp)
        | (with_reducible apply RDo.IsMarkov.mBind)
        | (with_reducible apply RDo.IsMarkov.forInList)
        | (with_reducible apply RDo.isProbabilityMeasure_of_isMarkov)
        | (with_reducible refine RDo.IsMarkov.comp ?_ ?_ <;>
            first | assumption | infer_instance | fun_prop)
        | (intro _; intros;
            first | (change RDo.IsMarkov _) | (change IsProbabilityMeasure _)))

end RDo
