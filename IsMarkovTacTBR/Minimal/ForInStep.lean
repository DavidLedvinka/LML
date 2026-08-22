/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.IsMarkov

/-!
# Measurability of the loop-control type `ForInStep`

The body of an `rdo` `for` loop does not return the next state `b : β` but a `ForInStep β`, which
also records whether the loop should stop (`ForInStep.done`) or go on (`ForInStep.yield`).
Reasoning about a loop therefore requires knowing that case analysis on a `ForInStep` is
measurable.

The σ-algebra chosen in `LeanMachineLearning.RDo.MeasurableSpaceMonad` is
`mβ.map ForInStep.yield ⊓ mβ.map ForInStep.done`: a set is measurable exactly when both of its
traces along the two constructors are. In other words `ForInStep β` is the coproduct of two copies
of `β`, and is therefore measurably isomorphic to `Bool × β`. All the proofs below rest on that
identification.

## Main statements

* `RDo.measurable_forInStepCasesOn`: case analysis on a `ForInStep` is measurable.
* `RDo.IsMarkov.forInStepCasesOn`: the `IsMarkov` counterpart, which is what the body of a loop
  produces after its last `mBind`.
-/

@[expose] public section

open MeasureTheory

namespace ForInStep

variable {β : Type*}

/-- `s.isDone` is `true` exactly when the loop step `s` requests early termination. Together with
`ForInStep.run` it realises the bijection `ForInStep β ≃ Bool × β`. -/
def isDone : ForInStep β → Bool
  | .done _ => true
  | .yield _ => false

@[simp] lemma isDone_done (b : β) : (ForInStep.done b).isDone = true := rfl

@[simp] lemma isDone_yield (b : β) : (ForInStep.yield b).isDone = false := rfl

end ForInStep

namespace RDo

variable {γ δ β : Type*} [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace β]

/-- `ForInStep.yield` is measurable: by definition of the σ-algebra, a measurable set of
`ForInStep β` has a measurable trace along `yield`. -/
@[fun_prop]
theorem measurable_yield : Measurable (ForInStep.yield : β → ForInStep β) := fun _ hs => hs.1

/-- Both traces of the preimage of a measurable set under `run` are that set itself. -/
@[fun_prop]
theorem measurable_run : Measurable (ForInStep.run : ForInStep β → β) := fun _ hs => ⟨hs, hs⟩

/-- The preimage of any set of booleans under `isDone` has `∅` or `univ` as traces. -/
@[fun_prop]
theorem measurable_isDone : Measurable (ForInStep.isDone : ForInStep β → Bool) := by
  intro s _
  constructor <;>
  · change MeasurableSet (_ ⁻¹' (ForInStep.isDone ⁻¹' s))
    first
    | (by_cases h : (false : Bool) ∈ s
       · convert MeasurableSet.univ using 1; ext b; simp [h]
       · convert MeasurableSet.empty using 1; ext b; simp [h])
    | (by_cases h : (true : Bool) ∈ s
       · convert MeasurableSet.univ using 1; ext b; simp [h]
       · convert MeasurableSet.empty using 1; ext b; simp [h])

/-- Case analysis on a `ForInStep` preserves measurability.

The proof rewrites the case analysis as the test `if q.2.isDone then _ else _`, which reduces it
to the measurability of `isDone` and of `run`. -/
theorem measurable_forInStepCasesOn {G H : γ → β → δ}
    (hG : Measurable fun p : γ × β => G p.1 p.2) (hH : Measurable fun p : γ × β => H p.1 p.2) :
    Measurable fun q : γ × ForInStep β =>
      ForInStep.casesOn (motive := fun _ => δ) q.2 (G q.1) (H q.1) := by
  have key : (fun q : γ × ForInStep β =>
        ForInStep.casesOn (motive := fun _ => δ) q.2 (G q.1) (H q.1))
      = fun q : γ × ForInStep β => if q.2.isDone then G q.1 q.2.run else H q.1 q.2.run := by
    ext ⟨c, s⟩; cases s <;> simp [ForInStep.run]
  rw [key]
  refine Measurable.ite ?_ ?_ ?_
  · exact (measurable_isDone.comp measurable_snd) (measurableSet_singleton true)
  · exact hG.comp (measurable_fst.prodMk (measurable_run.comp measurable_snd))
  · exact hH.comp (measurable_fst.prodMk (measurable_run.comp measurable_snd))

/-- Case analysis on a `ForInStep` between two Markov kernels is a Markov kernel: measurable by
`RDo.measurable_forInStepCasesOn`, and a probability measure in each of the two cases. -/
theorem IsMarkov.forInStepCasesOn {α : Type*} [MeasurableSpace α] {G H : γ → β → Measure α}
    (hG : IsMarkov fun p : γ × β => G p.1 p.2) (hH : IsMarkov fun p : γ × β => H p.1 p.2) :
    IsMarkov fun q : γ × ForInStep β =>
      ForInStep.casesOn (motive := fun _ => Measure α) q.2 (G q.1) (H q.1) := by
  refine ⟨measurable_forInStepCasesOn hG.measurable hH.measurable, ?_⟩
  rintro ⟨c, s⟩
  cases s with
  | done b => exact hG.isProbabilityMeasure (c, b)
  | yield b => exact hH.isProbabilityMeasure (c, b)

end RDo
