/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.RDo
public import LeanMachineLearning.RDo.Tactic.Elab
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# `is_markov` at work

Four examples, in increasing order of what the tactic leaves to do. They double as regression
tests: what the comments claim `is_markov` closes is what it closes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RDo

namespace RDo.Examples

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-! ### A closed program -/

/-- The sum of two independent samples of `μ`. -/
noncomputable def init : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y

example : IsProbabilityMeasure (init μ) := by
  -- No `unfold` needed: the tactic looks through `init` itself.
  -- The tactic crosses the two `let x ← _` and the `return`, closes the two occurrences of `μ`
  -- by `RDo.IsMarkov.const`, and hands the measurability condition of the `return` to `fun_prop`.
  is_markov

/-! ### A program with a parameter

Nothing changes: the parameter of the program is simply the parameter the recursion starts from,
instead of `Unit`. -/

example : IsMarkov fun c : ℝ ↦ (rdo
    let y ← μ
    return c + y : Measure ℝ) := by
  -- The condition `fun_prop` discharges is `Measurable fun c : ℝ × ℝ ↦ c.1 + c.2`: the
  -- parameter has grown by one component per binder crossed.
  is_markov

/-! ### Sampling from a kernel

`let y ← κ x` is not one of the two constructs an `rdo` block is made of: it is a Markov kernel
`κ` read through a function of the parameter. `RDo.Tactic.Shape.comp` recognises that shape,
`RDo.IsMarkov.ofKernel` closes the `κ` part, and the reparametrisation shows up as one more
measurability goal. -/

/-- One step driven by a Mathlib kernel. -/
noncomputable def step (κ : Kernel ℝ ℝ) : Measure ℝ := rdo
  let x ← μ
  let y ← κ x
  return x + y

example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] : IsProbabilityMeasure (step μ κ) := by
  -- Two measurability conditions this time: the reparametrisation `c ↦ c.2` through which `κ` is
  -- read, and the usual one of the final `return`. Both go to `fun_prop`.
  is_markov

/-! ### What the local context is used for

`fun_prop` reads the local hypotheses, so a measurability fact that has to be assumed only needs
to be in scope. Nothing else changes. -/

/-- A function nothing is known about. -/
opaque weird : ℝ → ℝ

example (hw : Measurable weird) : IsProbabilityMeasure (rdo
    let x ← μ
    return weird x : Measure ℝ) := by
  -- `is_markov` produces `Measurable fun c : Unit × ℝ ↦ weird c.2`, and `fun_prop` proves it
  -- from `hw`. Without `hw` in the context, that goal is what the tactic would hand back.
  is_markov

noncomputable def shift : Measure ℝ := rdo
  let x ← μ
  return x + 1

noncomputable def test : Measure ℝ := rdo
  let z ← shift μ
  return z

example : IsProbabilityMeasure (test μ) := by
  is_markov

noncomputable def test_ite : Measure ℝ := rdo
  let x ← μ
  if x < 0 then
    return x
  else
    return x + 1

example : IsProbabilityMeasure (test_ite μ) := by
  is_markov

variable (s : Set ℝ) {hs : MeasurableSet s} (ν : Kernel s ℝ) (ν' : Kernel (sᶜ : Set ℝ) ℝ)
  [IsMarkovKernel ν] [IsMarkovKernel ν']

open Classical in
noncomputable def depBranch : Measure ℝ := rdo
  let x ← μ
  if hx : x ∈ s then
    let y ← ν ⟨x, hx⟩
    return x + y
  else
    let y ← ν' ⟨x, hx⟩
    return y

open Classical in
example : IsProbabilityMeasure (depBranch μ s ν ν') := by
  is_markov

end RDo.Examples
