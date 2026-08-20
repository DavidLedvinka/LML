/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.IsMarkov
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# `IsMarkov` is stable under `rdo`'s `let x ← _` and `return`

An `rdo` block is built from exactly two operations: `mPure` (written `return`) and `mBind`
(written `let x ← _`). This file shows that `RDo.IsMarkov` is preserved by both, which is all one
needs for a straight-line program.

The only real work is `RDo.measurable_bind`: `Measure.measurable_bind'` in Mathlib keeps the
kernel fixed and varies the measure, whereas an `rdo` program varies both with the parameter.

## Main statements

* `RDo.IsMarkov.mPure_comp`: `return e` is a Markov kernel when `e` is measurable.
* `RDo.IsMarkov.mBind`: `let x ← p; q` is a Markov kernel when `p` and `q` are.
* `RDo.isProbabilityMeasure_mBind`: a closed program `let x ← μ; q` is a probability measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open MeasurableSpacePure MeasurableSpaceBind

namespace RDo

universe u

-- `mBind` forces the two types of a `rdo` block to live in the same universe.
variable {γ : Type*} {α β : Type u} [MeasurableSpace γ] [MeasurableSpace α] [MeasurableSpace β]

/-- `return e`, i.e. the Dirac mass, is a Markov kernel. -/
instance isMarkov_mPure : IsMarkov (mPure : α → Measure α) :=
  ⟨show Measurable (Measure.dirac : α → Measure α) from Measure.measurable_dirac,
    fun a => by rw [mPure_def]; infer_instance⟩

/-- `rdo`'s `return e`, for a measurable expression `e` depending on the parameter. -/
theorem IsMarkov.mPure_comp {g : γ → α} (hg : Measurable g := by fun_prop) :
    IsMarkov fun c => (mPure (g c) : Measure α) :=
  isMarkov_mPure.comp hg

/-- Binding a Markov kernel `κ` with a family `η` that is jointly measurable in the parameter and
in the bound variable is measurable in the parameter.

Unfolding the value on a measurable set turns the goal into the measurability of
`c ↦ ∫⁻ a, η c a s ∂(κ c)`, which is exactly `Measurable.lintegral_kernel_prod_right` for the
kernel attached to `κ`. -/
theorem measurable_bind {κ : γ → Measure α} [IsMarkov κ] {η : γ → α → Measure β}
    (hη : Measurable (uncurry η)) : Measurable fun c => (κ c).bind (η c) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hηc : ∀ c, Measurable (η c) := fun c => hη.comp (measurable_const.prodMk measurable_id)
  simp_rw [Measure.bind_apply hs (hηc _).aemeasurable]
  exact Measurable.lintegral_kernel_prod_right (κ := IsMarkov.toKernel κ)
    ((Measure.measurable_coe hs).comp hη)

/-- `rdo`'s `let x ← p; q`. Note the shape of `hη`: the bound variable `x` joins the parameter, so
what is required of the continuation is joint measurability in `(parameter, x)`. -/
theorem IsMarkov.mBind {κ : γ → Measure α} (hκ : IsMarkov κ) {η : γ → α → Measure β}
    (hη : IsMarkov fun p : γ × α => η p.1 p.2) : IsMarkov fun c => κ c >>=ₘ η c := by
  have hη' : Measurable (uncurry η) := hη.measurable
  refine ⟨?_, fun c => ?_⟩
  · simpa only [mBind_def] using measurable_bind (κ := κ) hη'
  · rw [mBind_def]
    have := hκ.isProbabilityMeasure c
    exact isProbabilityMeasure_bind (hη'.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (.of_forall fun a => hη.isProbabilityMeasure (c, a))

/-- A program with no parameter, `let x ← μ; q`, denotes a probability measure. This is the last
step of a proof about a closed program. -/
theorem isProbabilityMeasure_mBind {μ : Measure α} [IsProbabilityMeasure μ] {η : α → Measure β}
    (hη : IsMarkov η) : IsProbabilityMeasure (μ >>=ₘ η) := by
  rw [mBind_def]
  exact isProbabilityMeasure_bind hη.measurable.aemeasurable (.of_forall hη.isProbabilityMeasure)

end RDo
