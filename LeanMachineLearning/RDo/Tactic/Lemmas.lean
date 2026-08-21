/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.Tactic.Basic
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# One lemma per `rdo` construct

This file is the table the tactic reads: to every construct an `rdo` block can be made of, it
associates the single lemma that reduces an `IsMarkov` goal about it to `IsMarkov` goals about its
sub-programs, plus measurability side conditions.

To extend the tactic, add a lemma here in the same shape — conclusion `IsMarkov fun c ↦ ...`,
hypotheses either `IsMarkov ...` or `Measurable ...` — and one case in
`LeanMachineLearning.RDo.Tactic.Elab`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open MeasurableSpacePure MeasurableSpaceBind

namespace RDo.IsMarkov

universe u

-- `mBind` forces the two types of an `rdo` block to live in the same universe.
variable {γ γ' : Type*} {α β : Type u} [MeasurableSpace γ] [MeasurableSpace γ'] [MeasurableSpace α]
  [MeasurableSpace β]

/-- `rdo`'s `return e`, for an expression `e` depending measurably on the parameter.

`mPure` is `MeasureTheory.Measure.dirac`, so there is nothing to prove beyond the measurability
of `e`, which is exactly the side condition the tactic hands back to the user. -/
theorem mPure_comp {g : γ → α} (hg : Measurable g) :
    IsMarkov fun c ↦ (mPure (g c) : Measure α) :=
  ⟨show Measurable fun c ↦ Measure.dirac (g c) from Measure.measurable_dirac.comp hg,
    fun c ↦ by rw [mPure_def]; infer_instance⟩

/-- Binding a Markov kernel `κ` with a family `η` that is jointly measurable in the parameter and
in the bound variable is measurable in the parameter.

`Measure.measurable_bind'` in Mathlib keeps the kernel fixed and varies the measure, whereas an
`rdo` program varies both with the parameter; hence this lemma. Unfolding the value on a
measurable set turns the goal into the measurability of `c ↦ ∫⁻ a, η c a s ∂(κ c)`, which is
`Measurable.lintegral_kernel_prod_right` for the kernel attached to `κ`. -/
theorem _root_.RDo.measurable_bind {κ : γ → Measure α} (hκ : IsMarkov κ) {η : γ → α → Measure β}
    (hη : Measurable (uncurry η)) : Measurable fun c ↦ (κ c).bind (η c) := by
  -- `κ` seen as a bundled Mathlib kernel, which is what the lemma below expects.
  let κ' : Kernel γ α := ⟨κ, hκ.measurable⟩
  have : IsMarkovKernel κ' := ⟨fun c ↦ hκ.isProbabilityMeasure c⟩
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have hηc : ∀ c, Measurable (η c) := fun c ↦ hη.comp (measurable_const.prodMk measurable_id)
  simp_rw [Measure.bind_apply hs (hηc _).aemeasurable]
  exact Measurable.lintegral_kernel_prod_right (κ := κ') ((Measure.measurable_coe hs).comp hη)

/-- `rdo`'s `let x ← p; q`.

Note the shape of `hη`: crossing a bind moves the bound variable `x` into the parameter, so what
is required of the continuation is joint measurability in `(parameter, x)`. This is why the
parameter of an `IsMarkov` goal grows into a nested product as the tactic descends into the
program. -/
theorem mBind {κ : γ → Measure α} (hκ : IsMarkov κ) {η : γ → α → Measure β}
    (hη : IsMarkov fun p : γ × α ↦ η p.1 p.2) : IsMarkov fun c ↦ κ c >>=ₘ η c := by
  have hη' : Measurable (uncurry η) := hη.measurable
  refine ⟨?_, fun c ↦ ?_⟩
  · simpa only [mBind_def] using measurable_bind hκ hη'
  · rw [mBind_def]
    have := hκ.isProbabilityMeasure c
    exact isProbabilityMeasure_bind (hη'.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (.of_forall fun a ↦ hη.isProbabilityMeasure (c, a))

/-- Composing a Markov kernel with a measurable map is a Markov kernel. -/
theorem comp {κ : γ → Measure α} (hκ : IsMarkov κ) {g : γ' → γ} (hg : Measurable g) :
    IsMarkov fun c ↦ κ (g c) :=
  ⟨hκ.measurable.comp hg, fun _ ↦ hκ.isProbabilityMeasure _⟩

/-- A measurable two-way branch between Markov kernels is a Markov kernel. -/
theorem ite {p : γ → Prop} [DecidablePred p] (hp : Measurable p)
    {κ η : γ → Measure α} (hκ : IsMarkov κ) (hη : IsMarkov η) :
    IsMarkov fun c ↦ if p c then κ c else η c := by
  refine ⟨hκ.measurable.ite hp.setOf hη.measurable, fun c ↦ ?_⟩
  by_cases h : p c
  · simpa [h] using hκ.isProbabilityMeasure c
  · simpa [h] using hη.isProbabilityMeasure c

theorem dite {p : γ' → γ} (hp : Measurable p) {s : Set γ} (hs : MeasurableSet s)
    [∀ x, Decidable (x ∈ s)] {κ : s → Measure α} (hκ : IsMarkov κ)
    {η : (sᶜ : Set γ) → Measure α} (hη : IsMarkov η) :
    IsMarkov fun c ↦ if h : (p c) ∈ s then κ ⟨p c, h⟩ else η ⟨p c, h⟩ := by
  refine ⟨(hκ.measurable.dite hη.measurable hs).comp hp, fun c ↦ ?_⟩
  · by_cases h : p c ∈ s
    · simpa [h] using hκ.isProbabilityMeasure _
    · simpa [h] using hη.isProbabilityMeasure _

/-- The form of `RDo.IsMarkov.dite` an `rdo` program actually produces.

`if h : p c then … else …` elaborates to branches indexed by the *proof* `h`, not by an element
of a subtype. Passing from one to the other — `κ ⟨c, h⟩` against `κ' c h` — is a higher-order
problem `apply` does not solve, which is why the tactic builds this application itself, from the
pieces `RDo.Tactic.shapeOf` extracted.

Stating the side condition as `Measurable p` rather than `MeasurableSet {c | p c}` keeps it
within reach of `fun_prop`; `Measurable.setOf` bridges the two, once, here. -/
theorem diteP {p : γ → Prop} [inst : DecidablePred p] (hp : Measurable p)
    {κ : {c // p c} → Measure α} (hκ : IsMarkov κ)
    {η : {c // ¬ p c} → Measure α} (hη : IsMarkov η) :
    IsMarkov fun c ↦ if h : p c then κ ⟨c, h⟩ else η ⟨c, h⟩ := by
  refine ⟨.dite (s := {c | p c}) hκ.measurable hη.measurable hp.setOf, fun c ↦ ?_⟩
  by_cases h : p c
  · simpa [h] using hκ.isProbabilityMeasure _
  · simpa [h] using hη.isProbabilityMeasure _

end RDo.IsMarkov
