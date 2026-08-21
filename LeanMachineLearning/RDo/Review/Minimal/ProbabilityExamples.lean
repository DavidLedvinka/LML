/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.Tactic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Two `rdo` programs, proved step by step

This file is the point of the three previous ones. It proves, without any automation beyond
`fun_prop` for the measurability side conditions, that

* `RDo.Examples.init μ` is a probability measure;
* `RDo.Examples.iter μ` is a Markov kernel in its history argument.

Each proof follows the shape of the program: one lemma per `rdo` construct, in the same order.
The `is_markov` tactic of `LeanMachineLearning.RDo.Tactic` chains exactly those lemmas; both
proofs are also given in that one-line form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MeasurableSpacePure MeasurableSpaceBind

namespace RDo.Examples

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-! ### A straight-line program

`init μ` elaborates to `μ >>=ₘ fun x => μ >>=ₘ fun y => mPure (x + y)`. -/

/-- The sum of two independent samples of `μ`. -/
noncomputable def init : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y

example : IsProbabilityMeasure (init μ) := by
  unfold init
  -- The program is `μ >>=ₘ η`, with no parameter: `isProbabilityMeasure_mBind` peels off the
  -- outer bind and leaves the continuation to prove.
  refine isProbabilityMeasure_mBind ?_
  -- ⊢ IsMarkov fun x => μ >>=ₘ fun y => mPure (x + y)
  -- The parameter is now `x : ℝ`, and the program is again a bind.
  refine IsMarkov.mBind ?_ ?_
  -- The left-hand side `μ` does not depend on `x`.
  · exact IsMarkov.const μ
  -- ⊢ IsMarkov fun p : ℝ × ℝ => mPure (p.1 + p.2)
  -- Crossing a bind moves the bound variable `y` into the parameter, which becomes the pair
  -- `p = (x, y)`. All that is left is the measurability of `p ↦ p.1 + p.2`.
  · exact IsMarkov.mPure_comp (by fun_prop)

/-- The same proof written as a single term. -/
example : IsProbabilityMeasure (init μ) :=
  isProbabilityMeasure_mBind <|
    (IsMarkov.const μ).mBind (IsMarkov.mPure_comp (by fun_prop))

/-- And the same proof left to the tactic. -/
example : IsProbabilityMeasure (init μ) := by unfold init; is_markov

/-! ### A program with a loop and a parameter

`iter μ hist` elaborates to `(MeasurableSpaceForIn.forIn (List.range n) 0 body) >>=ₘ mPure`,
where `body a s = μ >>=ₘ fun y => mPure (ForInStep.yield (s + y))`. The history `hist` is not
used by the program, but it is the parameter of the kernel one wants to build. -/

/-- A random walk of `n` steps, as a function of a history it happens to ignore. -/
noncomputable def iter {n : ℕ} (_hist : Iic n → ℝ × ℝ) : Measure ℝ := rdo
  let mut x := 0
  for _ in List.range n rdo
    let y ← μ
    x := x + y
  return x

instance (n : ℕ) : IsMarkov (iter (n := n) μ) := by
  unfold iter
  -- The program is `(loop) >>=ₘ (fun x => return x)`.
  refine IsMarkov.mBind ?_ ?_
  -- ⊢ IsMarkov fun hist => forIn (List.range n) 0 body
  · -- The list `List.range n` is fixed, so `hf` may treat each element `_a` separately, and the
    -- initial state `0` is a constant function of the parameter.
    refine IsMarkov.forInList _ (fun _a => ?_) (by fun_prop)
    -- ⊢ IsMarkov fun p : (Iic n → ℝ × ℝ) × ℝ => μ >>=ₘ fun y => mPure (yield (p.2 + y))
    -- The parameter now carries the loop state: `p = (hist, x)`.
    refine IsMarkov.mBind ?_ ?_
    · exact IsMarkov.const μ
    -- ⊢ IsMarkov fun q : ((Iic n → ℝ × ℝ) × ℝ) × ℝ => mPure (yield (q.1.2 + q.2))
    -- One more bind, so one more component: `q = ((hist, x), y)`.
    · exact IsMarkov.mPure_comp (by fun_prop)
  -- ⊢ IsMarkov fun p : (Iic n → ℝ × ℝ) × ℝ => mPure p.2
  · exact IsMarkov.mPure_comp measurable_snd

/-- And the same proof left to the tactic. -/
example (n : ℕ) : IsMarkov (iter (n := n) μ) := by unfold iter; is_markov

/-- Being `IsMarkov` is what makes the program usable as a Mathlib kernel. -/
noncomputable def iterKernel (n : ℕ) : Kernel (Iic n → ℝ × ℝ) ℝ :=
  IsMarkov.toKernel (iter (n := n) μ)

instance (n : ℕ) : IsMarkovKernel (iterKernel μ n) := by
  unfold iterKernel
  infer_instance

/-- And it also gives back the pointwise statement. -/
example (n : ℕ) (hist : Iic n → ℝ × ℝ) : IsProbabilityMeasure (iter μ hist) :=
  IsMarkov.isProbabilityMeasure (κ := iter (n := n) μ) hist

/-- Which the tactic reaches directly, through `RDo.isProbabilityMeasure_of_isMarkov`. -/
example (n : ℕ) (hist : Iic n → ℝ × ℝ) : IsProbabilityMeasure (iter μ hist) := by
  unfold iter; is_markov

end RDo.Examples
