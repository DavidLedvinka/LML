module

public import LeanMachineLearning.RDo.MonadInstances
public import LeanMachineLearning.RDo.ForInInstances
public import LeanMachineLearning.RDo.Tactic
public import Mathlib

@[expose] public section

open MeasureTheory Measure Finset RDo ProbabilityTheory

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

noncomputable def init : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y

noncomputable def iter {n : ℕ} (_hist : Iic n → ℝ × ℝ) : Measure ℝ := rdo
  let mut x := 0
  for _ in List.range n rdo
    let y ← μ
    x := x + y
  return x

instance (n : ℕ) : IsMarkov (iter (n := n) μ) := by
  unfold iter
  refine IsMarkov.mBind ?_ ?_
  · -- la boucle : collection fixe `List.range n`, état initial constant `0`
    refine IsMarkov.forInList _ (fun _a => ?_) (by fun_prop)
    -- le corps, à élément `_a` fixé : `let y ← μ`
    refine IsMarkov.mBind (IsMarkov.const μ) ?_
    -- la mise à jour `x := x + y`, c.-à-d. `return (yield (x + y))`
    exact IsMarkov.mPure_comp (by fun_prop)
  · -- la continuation finale : `return x`
    exact IsMarkov.mPure_comp measurable_snd

noncomputable def iter_kernel (n : ℕ) : Kernel (Iic n → ℝ × ℝ) ℝ :=
  IsMarkov.toKernel (iter (n := n) μ)

instance (n : ℕ) : IsMarkovKernel (iter_kernel μ n) := by
  unfold iter_kernel
  infer_instance

instance : IsProbabilityMeasure (init μ) := by
  unfold init
  is_markov

/- Ce que `is_markov` fait à la main, sur `init` : le programme est un `mBind`, donc il suffit de
savoir que `μ` est une proba et que la continuation est un noyau markovien. -/
example : IsProbabilityMeasure (init μ) :=
  isProbabilityMeasure_mBind <|
    (IsMarkov.const (γ := ℝ) μ).mBind (IsMarkov.mPure_comp (by fun_prop))

example : IsProbabilityMeasure (init μ) := by
  apply isProbabilityMeasure_mBind
  refine IsMarkov.mBind ?_ ?_
  · exact IsMarkov.const μ
  · exact IsMarkov.mPure_comp
