module

public import LeanMachineLearning.RDo.MonadInstances
public import LeanMachineLearning.RDo.ForInInstances
public import Mathlib

@[expose] public section

open MeasureTheory Measure Finset

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

noncomputable def init : Measure ℝ := rdo
  let x ← μ
  return x

noncomputable def iter {n : ℕ} (_hist : Iic n → ℝ × ℝ) : Measure ℝ := rdo
  let mut x := 0
  for _ in List.range n rdo
    let y ← μ
    x := x + y
  return x

example {n : ℕ} (_hist : Iic n → ℝ × ℝ) : IsProbabilityMeasure (iter μ _hist) := by
  unfold iter
  simp
  sorry

/- example : IsProbabilityMeasure (init μ) := by
  unfold init
  simp only [mPure_def, mBind_def]
  refine ⟨?_⟩
  rw [Measure.bind_apply (MeasurableSet.univ)]
  · have hker : ∀ x : ℝ, Measurable fun y ↦ dirac (x + y) := by
      intro x
      exact measurable_dirac.comp <| measurable_const_add x
    simp_rw [Measure.bind_apply (MeasurableSet.univ) (hker _).aemeasurable]
    simp
  · apply Measurable.aemeasurable
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    have hker : ∀ x : ℝ, Measurable fun y : ℝ ↦ (dirac (x + y) : Measure ℝ) := fun x =>
      measurable_dirac.comp (measurable_const_add x)
    simp_rw [Measure.bind_apply hs (hker _).aemeasurable, dirac_apply' _ hs]
    exact ((measurable_one.indicator hs).comp measurable_add).lintegral_prod_right' -/
