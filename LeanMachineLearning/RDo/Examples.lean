module

public import LeanMachineLearning.RDo.Monad.Instances
public import LeanMachineLearning.RDo.Monad.ForInInstances
public import LeanMachineLearning.RDo.Tactic.Elab
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Algorithm
public import Mathlib

set_option linter.style.header false

@[expose] public section

open MeasureTheory ProbabilityTheory Measure

/- # Nonpolymorphic examples -/

universe u v

noncomputable def measureSample : Measure Bool := rdo
  let x ← bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩
  let y ← bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩
  return x + y

instance : IsProbabilityMeasure measureSample := by
  is_markov

def pseudoSample : Rand Bool := do
  let x ← Random.randBool
  let y ← Random.randBool
  return x + y

/- # Polymorphic examples -/

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]

class HasBit (m : (α : Type) → MeasurableSpace α → Type v) where
  bit : m Bool (by infer_instance)

noncomputable instance : HasBit Measure where
  bit := bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩

instance : HasBit PseudoRandomM where
  bit := Random.randBool

def indepAnd [HasBit m] : m Bool := rdo
  let x ← HasBit.bit
  let y ← HasBit.bit
  return x && y

noncomputable def indepAndMeasure : Measure Bool := indepAnd (m := Measure)

def indepAndGen : PseudoRandomM Bool := indepAnd (m := PseudoRandomM)

variable {α : Type*} [MeasurableSpace α]

def sampleBitsArray [HasBit m] (n : ℕ) : m (Array Bool) := rdo
  let mut xs : Array Bool := #[]
  for _ in List.range n rdo
    let b ← HasBit.bit (m := m)
    xs := xs.push b
  return xs

variable (μ : Measure ℝ) (as : List ℝ) [IsProbabilityMeasure μ]

variable (n : ℕ) (f : Vector ℝ n → Vector ℝ n) (hf : Measurable f)

def tt := μ

noncomputable
def test (vs : Vector ℝ n) : Measure ℝ := rdo
  let mut x ← μ
  for i in f vs rdo
    x := x + i
  return x

example : IsMarkov (test μ n f) := by
  is_markov

variable (νs : List (Measure ℝ)) (h : ∀ ν ∈ νs, IsProbabilityMeasure ν)

noncomputable
def test2 : Measure ℝ := rdo
  let mut x := 0
  for w in νs rdo
    let y ← w
    x := x + y
  return x

example : IsProbabilityMeasure (test2 νs) := by
  is_markov


/- # Thompson sampling -/

/-- Gaussian Thompson sampling: rewards have known variance `1` and each arm has an independent
`N(0, 1)` prior. `N j` is the posterior precision of arm `j` and `S j` its sum of rewards, so
`θ j` is sampled from the posterior `N(S j / N j, 1 / N j)`. The argmax is played. -/
noncomputable def thompson {K n : ℕ} (hK : 0 < K) (history : Vector (Fin K × ℝ) n) :
    Measure (Fin K) := rdo
  let mut N : Fin K → ℝ := fun _ ↦ 1
  let mut S : Fin K → ℝ := fun _ ↦ 0
  for (a, r) in history rdo
    N := fun j ↦ if j = a then N j + 1 else N j
    S := fun j ↦ if j = a then S j + r else S j
  let mut θ : Fin K → ℝ := fun _ ↦ 0
  for j in List.finRange K rdo
    let z ← gaussianReal (S j / N j) (Real.toNNReal (1 / N j))
    θ := fun k ↦ if k = j then z else θ k
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  return argmax θ

variable {K n : ℕ} (hK : 0 < K)

instance : IsMarkov (thompson (n := n) hK) := by
  is_markov
  · refine ForInStep.measurable_yield.comp ?_
    refine Measurable.prodMk ?_ ?_
    · refine measurable_pi_lambda _ fun k ↦ ?_
      refine Measurable.ite (by measurability) ?_ ?_
      · fun_prop
      · fun_prop
    · refine measurable_pi_lambda _ fun k ↦ ?_
      refine Measurable.ite (by measurability) ?_ ?_
      · fun_prop
      · fun_prop
  · intro i hi
    refine ForInStep.measurable_yield.comp ?_
    refine measurable_pi_lambda _ fun k ↦ ?_
    refine Measurable.ite (by measurability) ?_ ?_
    · fun_prop
    · fun_prop

instance : IsMarkovKernel <| IsMarkov.toKernel (thompson (n := n) hK) := inferInstance

/- open Learning

example : Algorithm (Fin K) ℝ where
  policy n :=
    (IsMarkov.toKernel (thompson (n := n) hK)).comap Vector.equivFn (by fun_prop) -/

end
