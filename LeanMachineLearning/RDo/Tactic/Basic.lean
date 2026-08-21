/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.MonadInstances
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# `IsMarkov`, the predicate the tactic reasons about

An `rdo` program in the `MeasureTheory.Measure` monad denotes a measure, and one wants to know
that this measure is a probability measure. That property alone is not stable under `>>=ₘ`: to say
anything about `μ >>=ₘ η` one also needs `η` to be *measurable*, since that is the side condition
of `MeasureTheory.Measure.bind`.

What is stable is the conjunction of the two, i.e. being a Markov kernel. This file defines it,
plus the two facts that let the tactic start and stop:

* `RDo.isProbabilityMeasure_of_isMarkov` turns a goal about a closed program into an `IsMarkov`
  goal, which is the only form the tactic knows;
* `RDo.IsMarkov.const` closes the leaves, where a fixed distribution such as `μ` is reached.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RDo

variable {γ α : Type*} [MeasurableSpace γ] [MeasurableSpace α]

/-- `IsMarkov κ` states that the family of measures `κ : γ → Measure α` is a *Markov kernel*:
it is measurable, and every `κ c` is a probability measure.

Read `γ` as the type of everything the program has in scope: its own parameters, and the
variables bound by the `let x ← _` it sits under. -/
class IsMarkov (κ : γ → Measure α) : Prop where
  /-- A Markov kernel is measurable as a map into the Giry monad. -/
  measurable : Measurable κ
  /-- A Markov kernel takes values in probability measures. -/
  isProbabilityMeasure (c : γ) : IsProbabilityMeasure (κ c)

/-- A Markov kernel is a family of probability measures. -/
instance IsMarkov.ofKernel (κ : Kernel γ α) [IsMarkovKernel κ] : IsMarkov κ :=
  ⟨κ.measurable, fun _ ↦ inferInstance⟩

/-- A family that does not depend on the parameter is a Markov kernel as soon as its value is a
probability measure.

This is an `instance` on purpose: it is what the tactic uses, through instance synthesis, to close
a leaf such as `fun _ ↦ μ`. -/
instance IsMarkov.const (μ : Measure α) [IsProbabilityMeasure μ] : IsMarkov fun _ : γ ↦ μ :=
  ⟨measurable_const, fun _ ↦ ‹_›⟩

/-- A program with no parameter denotes a probability measure as soon as the constant family it
defines is a Markov kernel.

The tactic applies this first, so that a goal `IsProbabilityMeasure t` becomes
`IsMarkov fun _ : Unit ↦ t` and the rest of the work happens in a single, uniform form. -/
theorem isProbabilityMeasure_of_isMarkov {μ : Measure α} (h : IsMarkov fun _ : Unit ↦ μ) :
    IsProbabilityMeasure μ :=
  h.isProbabilityMeasure ()

end RDo
