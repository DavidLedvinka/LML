/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.MonadInstances
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Basic

/-!
# `IsMarkov`: the invariant carried through an `rdo` program

An `rdo` program in the `MeasureTheory.Measure` monad denotes a measure, and one wants to know
that this measure is a probability measure. That property alone, however, is not stable under
`>>=ₘ`: to say anything about `μ >>=ₘ η` one also needs `η` to be *measurable*, since that is the
side condition of `MeasureTheory.Measure.bind`.

The property that *is* stable is therefore the conjunction of the two, i.e. being a Markov
kernel. This file defines it and gives the three ways of building one that do not involve the
`rdo` constructs themselves; those come in `LeanMachineLearning.RDo.Bind`.

## Main definitions

* `RDo.IsMarkov κ`: `κ : γ → Measure α` is measurable and every `κ c` is a probability measure.
* `RDo.IsMarkov.toKernel`: the corresponding bundled `ProbabilityTheory.Kernel`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RDo

variable {γ γ' α : Type*} [MeasurableSpace γ] [MeasurableSpace γ'] [MeasurableSpace α]

/-- `IsMarkov κ` states that the family of measures `κ : γ → Measure α` is a *Markov kernel*:
it is measurable, and every `κ c` is a probability measure.

A program `p : Measure α` with a parameter `c : γ` is a Markov kernel exactly when it is a
well-behaved building block for larger programs. -/
class IsMarkov (κ : γ → Measure α) : Prop where
  /-- A Markov kernel is measurable as a map into the Giry monad. -/
  measurable : Measurable κ
  /-- A Markov kernel takes values in probability measures. -/
  isProbabilityMeasure (c : γ) : IsProbabilityMeasure (κ c)

namespace IsMarkov

/-- A family that does not depend on the parameter is a Markov kernel as soon as its value is a
probability measure. This is how a fixed distribution such as `μ` enters a program. -/
instance const (μ : Measure α) [IsProbabilityMeasure μ] : IsMarkov fun _ : γ => μ :=
  ⟨measurable_const, fun _ => ‹_›⟩

/-- Reading the parameter through a measurable map preserves the Markov property. This is how a
sub-program that only sees part of the ambient parameter is handled. -/
theorem comp {κ : γ → Measure α} (hκ : IsMarkov κ) {g : γ' → γ}
    (hg : Measurable g := by fun_prop) : IsMarkov fun c => κ (g c) :=
  ⟨hκ.measurable.comp hg, fun _ => hκ.isProbabilityMeasure _⟩

/-- `IsMarkov` only depends on the pointwise values of the family. Used to replace a `match`
produced by the elaborator with the `casesOn` the lemmas are stated with. -/
theorem congr {κ η : γ → Measure α} (h : ∀ c, κ c = η c) (hη : IsMarkov η) : IsMarkov κ :=
  funext h ▸ hη

/-- The bundled Mathlib kernel attached to an `IsMarkov` family. -/
noncomputable def toKernel (κ : γ → Measure α) [IsMarkov κ] : Kernel γ α :=
  ⟨κ, IsMarkov.measurable⟩

instance isMarkovKernel_toKernel (κ : γ → Measure α) [IsMarkov κ] :
    IsMarkovKernel (toKernel κ) :=
  ⟨fun c => IsMarkov.isProbabilityMeasure (κ := κ) c⟩

end IsMarkov

/-- A program with no parameter denotes a probability measure as soon as the constant family it
defines is a Markov kernel.

`IsProbabilityMeasure` alone does not compose, `IsMarkov` does; this lemma is what lets a goal
about a closed program be attacked with the `IsMarkov` lemmas. The parameter type is `Unit`
because the program ignores it. -/
theorem isProbabilityMeasure_of_isMarkov {μ : Measure α} (h : IsMarkov fun _ : Unit => μ) :
    IsProbabilityMeasure μ :=
  h.isProbabilityMeasure ()

end RDo
