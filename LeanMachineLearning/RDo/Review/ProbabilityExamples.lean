/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.Probability
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Examples: `rdo` programs are probability measures

Worked examples of the API of `LeanMachineLearning.RDo.Probability`. They double as regression
tests for the `is_markov` tactic: every proof below is expected to be closed by
`unfold <program>; is_markov`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Measure RDo

namespace RDo.Examples

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-! ### Sequential sampling -/

/-- The sum of two independent samples. -/
noncomputable def sumOfTwo : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y

example : IsProbabilityMeasure (sumOfTwo μ) := by unfold sumOfTwo; is_markov

/-- The same, proved by hand: `sumOfTwo` is a `mBind`, so it suffices that `μ` is a probability
measure and that the continuation is a Markov kernel. -/
example : IsProbabilityMeasure (sumOfTwo μ) :=
  isProbabilityMeasure_mBind <|
    (IsMarkov.const (γ := ℝ) μ).mBind (IsMarkov.mPure_comp (by fun_prop))

/-- A program parametrised by its input is a Markov kernel, not just a probability measure.
This is the statement one needs to use the program as a step of a larger algorithm. -/
example : IsMarkov fun c : ℝ => (rdo
    let y ← μ
    return c + y : Measure ℝ) := by is_markov

/-! ### Composing with an arbitrary Markov kernel -/

/-- A transition step driven by a Mathlib kernel. -/
noncomputable def step (κ : Kernel ℝ ℝ) : Measure ℝ := rdo
  let x ← μ
  let y ← κ x
  return x + y

example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] : IsProbabilityMeasure (step μ κ) := by
  unfold step; is_markov

/-! ### Branching -/

/-- A program whose control flow depends on the value that was sampled. -/
noncomputable def branch : Measure ℝ := rdo
  let x ← μ
  if 0 ≤ x then
    let y ← μ
    return x + y
  else
    return x

example : IsProbabilityMeasure (branch μ) := by unfold branch; is_markov

/-! ### Loops -/

/-- A random walk of length `n`. -/
noncomputable def walk (n : ℕ) : Measure ℝ := rdo
  let mut x := 0
  for _ in List.range n rdo
    let y ← μ
    x := x + y
  return x

example (n : ℕ) : IsProbabilityMeasure (walk μ n) := by unfold walk; is_markov

/-- A loop over an `Array`, whose elements are used inside the body. -/
noncomputable def weightedSum (xs : Array ℝ) : Measure ℝ := rdo
  let mut s := 0
  for a in xs rdo
    let y ← μ
    s := s + a * y
  return s

example (xs : Array ℝ) : IsProbabilityMeasure (weightedSum μ xs) := by
  unfold weightedSum; is_markov

example : IsMarkov (weightedSum μ) := by
  unfold weightedSum; is_markov

/-- A loop over a `Vector`. -/
noncomputable def weightedSumVec {n : ℕ} (xs : Vector ℝ n) : Measure ℝ := rdo
  let mut s := 0
  for a in xs rdo
    let y ← μ
    s := s + a * y
  return s

example {n : ℕ} (xs : Vector ℝ n) : IsProbabilityMeasure (weightedSumVec μ xs) := by
  unfold weightedSumVec; is_markov

/-- A loop with a membership proof (`for h : a in xs`). -/
noncomputable def weightedSumMem (xs : List ℝ) : Measure ℝ := rdo
  let mut s := 0
  for _h : a in xs rdo
    let y ← μ
    s := s + a * y
  return s

example (xs : List ℝ) : IsProbabilityMeasure (weightedSumMem μ xs) := by
  unfold weightedSumMem; is_markov

/-- A loop with early termination. -/
noncomputable def walkWithBreak (n : ℕ) : Measure ℝ := rdo
  let mut x := 0
  for i in List.range n rdo
    let y ← μ
    x := x + y
    if i = 3 then break
  return x

example (n : ℕ) : IsProbabilityMeasure (walkWithBreak μ n) := by
  unfold walkWithBreak; is_markov

/-- A loop with an early `return`. The returned value is carried in an `Option`, whose measurable
structure is set up in `LeanMachineLearning.RDo.Measurable`. -/
noncomputable def walkWithReturn (n : ℕ) : Measure ℝ := rdo
  let mut x := 0
  for i in List.range n rdo
    let y ← μ
    x := x + y
    if i = 3 then return x
  return x

example (n : ℕ) : IsProbabilityMeasure (walkWithReturn μ n) := by
  unfold walkWithReturn; is_markov

/-! ### Programs seen as kernels in their input

A program whose input is a collection is a Markov kernel in that input, not merely a probability
measure for each fixed input. This is the statement needed to plug the program into a larger
algorithm. It requires the loop body to be measurable in the element being traversed as well,
which `is_markov` obtains from `fun_prop`.

Supported for `List` and `Array` collections. `Vector` is not, for want of a `MeasurableSpace`
instance on it. -/

example : IsMarkov (weightedSum μ) := by unfold weightedSum; is_markov

/-- The number of iterations may be the parameter too. -/
example : IsMarkov (walk μ) := by unfold walk; is_markov

/-- A program recording one sample per input, as a kernel from inputs to trajectories. -/
noncomputable def track (xs : Array ℝ) : Measure (Array ℝ) := rdo
  let mut hist : Array ℝ := #[]
  for a in xs rdo
    let y ← μ
    hist := hist.push (a * y)
  return hist

example : IsMarkov (track μ) := by unfold track; is_markov

/-! ### Accumulating the history

The state of the loop may be a container: this is the usual way of recording the trajectory of an
algorithm. The relevant measurability facts live in `LeanMachineLearning.RDo.Measurable`. -/

/-- A fair coin. -/
noncomputable def bit : Measure Bool := bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩

instance : IsProbabilityMeasure bit := by unfold bit; infer_instance

/-- `n` independent bits, stored in an array. -/
noncomputable def sampleBits (n : ℕ) : Measure (Array Bool) := rdo
  let mut xs : Array Bool := #[]
  for _ in List.range n rdo
    let b ← bit
    xs := xs.push b
  return xs

example (n : ℕ) : IsProbabilityMeasure (sampleBits n) := by unfold sampleBits; is_markov

/-- `n` samples, stored in a list. -/
noncomputable def sampleList (n : ℕ) : Measure (List ℝ) := rdo
  let mut xs : List ℝ := []
  for _ in List.range n rdo
    let y ← μ
    xs := y :: xs
  return xs

example (n : ℕ) : IsProbabilityMeasure (sampleList μ n) := by unfold sampleList; is_markov

/-- A composite state: the current value and the whole trajectory. -/
noncomputable def walkWithHistory (n : ℕ) : Measure (ℝ × Array ℝ) := rdo
  let mut s := 0
  let mut hist : Array ℝ := #[]
  for _ in List.range n rdo
    let y ← μ
    s := s + y
    hist := hist.push s
  return (s, hist)

example (n : ℕ) : IsProbabilityMeasure (walkWithHistory μ n) := by
  unfold walkWithHistory; is_markov

end RDo.Examples
