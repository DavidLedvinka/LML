/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.ForInInstances
public import LeanMachineLearning.RDo.Measurable
public import LeanMachineLearning.RDo.MonadInstances
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Probabilistic reasoning about `rdo` programs

A stochastic algorithm written with the `rdo` notation in the `MeasureTheory.Measure` monad
denotes a measure. This file provides the API needed to prove that such a measure is a
*probability* measure.

The whole development is organised around one predicate:

* `RDo.IsMarkov κ`, for `κ : γ → Measure α`, states that `κ` is a Markov kernel, i.e. that `κ`
  is measurable and that every `κ c` is a probability measure.

`IsMarkov` (rather than `IsProbabilityMeasure`) is the right invariant to propagate through an
`rdo` program: measurability of the continuation is exactly the side condition needed by
`MeasureTheory.Measure.bind`, so a bare `IsProbabilityMeasure` statement is not strong enough to
be closed under `>>=ₘ`.

## Main definitions

* `RDo.IsMarkov`: the Markov-kernel predicate described above.
* `RDo.IsMarkovForIn'` / `RDo.IsMarkovForIn`: collections whose `rdo` `for` loops preserve
  `IsMarkov`. Instances are provided for `List`, `Array` and `Vector`.

## Main statements

* `RDo.IsMarkov.mBind`, `RDo.IsMarkov.mPure_comp`, `RDo.IsMarkov.mMap`, `RDo.IsMarkov.ite`,
  `RDo.IsMarkov.forIn`, `RDo.IsMarkov.optionCases`: `IsMarkov` is closed under every construct an
  `rdo` block can produce (`let x ← _`, `return`, `<$>ₘ`, `if`, `for`, early `return`).
* `RDo.IsMarkov.forInList`, `RDo.IsMarkov.forInArray`: the same for a loop whose *collection*
  depends on the parameter, which is what one needs to see a program as a kernel in its input.
* `RDo.forIn_nil`, `RDo.forIn_cons`, `RDo.forIn_array`: the equations unrolling an `rdo` `for`
  loop over a list or an array; they hold in any `MeasurableSpaceMonad`.
* `RDo.isProbabilityMeasure_of_isMarkov`: a closed `rdo` program denoting an `IsMarkov` family
  denotes a probability measure.

The measurability side conditions are handled by `fun_prop`, using the lemmas of
`LeanMachineLearning.RDo.Measurable`.

## Tactic

The `is_markov` tactic chains the lemmas above and discharges the measurability side conditions
with `fun_prop` (and `measurability` for `MeasurableSet` goals). It closes goals of the form
`IsMarkov κ` and `IsProbabilityMeasure μ` where `κ` and `μ` are `rdo` programs:

```
example : IsProbabilityMeasure prog := by unfold prog; is_markov
```

Facts `IsMarkov κ` about the kernels appearing in the program are taken from the local context or
from instance search, so a program built out of already-known Markov kernels needs no extra work.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open MeasurableSpacePure MeasurableSpaceBind MeasurableSpaceFunctor

namespace RDo

universe uρ uα u v

/-! ### The `IsMarkov` predicate -/

variable {γ γ' : Type*} {α β : Type u}
  [MeasurableSpace γ] [MeasurableSpace γ'] [MeasurableSpace α] [MeasurableSpace β]

/-- `IsMarkov κ` states that the family of measures `κ : γ → Measure α` is a *Markov kernel*:
it is measurable and every `κ c` is a probability measure.

This is the invariant propagated through an `rdo` program by the `is_markov` tactic. -/
class IsMarkov (κ : γ → Measure α) : Prop where
  /-- A Markov kernel is measurable as a map into the Giry monad. -/
  measurable : Measurable κ
  /-- A Markov kernel takes values in probability measures. -/
  isProbabilityMeasure (c : γ) : IsProbabilityMeasure (κ c)

namespace IsMarkov

attribute [fun_prop] IsMarkov.measurable

theorem aemeasurable {κ : γ → Measure α} [IsMarkov κ] {μ : Measure γ} : AEMeasurable κ μ :=
  IsMarkov.measurable.aemeasurable

/-- The bundled Mathlib `ProbabilityTheory.Kernel` attached to an `IsMarkov` family. Use it to
transfer the results of this file to Mathlib's kernel API. -/
noncomputable def toKernel (κ : γ → Measure α) [IsMarkov κ] : Kernel γ α :=
  ⟨κ, IsMarkov.measurable⟩

@[simp] theorem toKernel_apply (κ : γ → Measure α) [IsMarkov κ] (c : γ) :
    toKernel κ c = κ c := rfl

@[simp] theorem coe_toKernel (κ : γ → Measure α) [IsMarkov κ] : ⇑(toKernel κ) = κ := rfl

instance isMarkovKernel_toKernel (κ : γ → Measure α) [IsMarkov κ] :
    IsMarkovKernel (toKernel κ) :=
  ⟨fun c => IsMarkov.isProbabilityMeasure (κ := κ) c⟩

/-- The `IsMarkov` predicate for the family attached to a Mathlib Markov kernel. -/
instance ofKernel (κ : Kernel γ α) [IsMarkovKernel κ] : IsMarkov (⇑κ) :=
  ⟨κ.measurable, fun _ => inferInstance⟩

end IsMarkov

/-- A closed `rdo` program whose (constant) family is `IsMarkov` denotes a probability measure. -/
theorem isProbabilityMeasure_of_isMarkov {μ : Measure α} (h : IsMarkov fun _ : PUnit.{u + 1} => μ) :
    IsProbabilityMeasure μ :=
  h.isProbabilityMeasure ⟨⟩

/-! ### Measurability of a dependent `bind` -/

/-- The dependent version of `MeasureTheory.Measure.measurable_bind'`: binding a measurable
family of Markov kernels along a Markov kernel is measurable in the parameter. -/
theorem measurable_bind {κ : γ → Measure α} [IsMarkov κ] {η : γ → α → Measure β}
    (hη : Measurable (uncurry η)) : Measurable fun c => (κ c).bind (η c) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hηc : ∀ c, Measurable (η c) := fun c => hη.comp (measurable_const.prodMk measurable_id)
  simp_rw [Measure.bind_apply hs (hηc _).aemeasurable]
  exact Measurable.lintegral_kernel_prod_right (κ := IsMarkov.toKernel κ)
    ((Measure.measurable_coe hs).comp hη)

/-! ### Closure properties of `IsMarkov` -/

namespace IsMarkov

/-- A constant family of probability measures is a Markov kernel. -/
instance const (μ : Measure α) [IsProbabilityMeasure μ] : IsMarkov fun _ : γ => μ :=
  ⟨measurable_const, fun _ => ‹_›⟩

/-- `IsMarkov` only depends on the pointwise values of the family. -/
theorem congr {κ η : γ → Measure α} (h : ∀ c, κ c = η c) (hη : IsMarkov η) : IsMarkov κ := by
  have : κ = η := funext h
  exact this ▸ hη

/-- Precomposing a Markov kernel with a measurable map gives a Markov kernel. -/
theorem comp {κ : γ → Measure α} (hκ : IsMarkov κ) {g : γ' → γ}
    (hg : Measurable g := by fun_prop) : IsMarkov fun c => κ (g c) :=
  ⟨hκ.measurable.comp hg, fun _ => hκ.isProbabilityMeasure _⟩

end IsMarkov

/-- `mPure` is a Markov kernel. -/
instance isMarkov_mPure : IsMarkov (mPure : α → Measure α) :=
  ⟨show Measurable (Measure.dirac : α → Measure α) from Measure.measurable_dirac,
    fun a => by rw [mPure_def]; infer_instance⟩

namespace IsMarkov

/-- `rdo`'s `return`/`pure`, applied to a measurable expression, is a Markov kernel. -/
theorem mPure_comp {g : γ → α} (hg : Measurable g := by fun_prop) :
    IsMarkov fun c => (mPure (g c) : Measure α) :=
  isMarkov_mPure.comp hg

/-- `rdo`'s `let x ← _` is a Markov kernel as soon as both sides are. This is the workhorse:
`hη` asks for joint measurability in the ambient parameter and in the bound variable. -/
theorem mBind {κ : γ → Measure α} (hκ : IsMarkov κ) {η : γ → α → Measure β}
    (hη : IsMarkov fun p : γ × α => η p.1 p.2) : IsMarkov fun c => κ c >>=ₘ η c := by
  have hη' : Measurable (uncurry η) := hη.measurable
  refine ⟨?_, fun c => ?_⟩
  · simpa only [mBind_def] using measurable_bind (κ := κ) hη'
  · rw [mBind_def]
    have := hκ.isProbabilityMeasure c
    exact isProbabilityMeasure_bind (hη'.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (.of_forall fun a => hη.isProbabilityMeasure (c, a))

/-- `rdo`'s `<$>ₘ` preserves the Markov property. -/
theorem mMap {κ : γ → Measure α} (hκ : IsMarkov κ) {g : γ → α → β}
    (hg : Measurable (uncurry g) := by fun_prop) :
    IsMarkov fun c => (g c <$>ₘ κ c : Measure β) := by
  have : ∀ c, (g c <$>ₘ κ c : Measure β) = κ c >>=ₘ fun a => mPure (g c a) := fun c =>
    (mMap_eq_mPure_mBind (hg.comp (measurable_const.prodMk measurable_id)) _)
  simp only [this]
  exact hκ.mBind (mPure_comp hg)

/-- A measurable two-way branch between Markov kernels is a Markov kernel. -/
theorem ite {p : γ → Prop} [DecidablePred p] (hp : MeasurableSet {c | p c})
    {κ η : γ → Measure α} (hκ : IsMarkov κ) (hη : IsMarkov η) :
    IsMarkov fun c => if p c then κ c else η c :=
  ⟨hκ.measurable.ite hp hη.measurable, fun c => by
    by_cases h : p c
    · simpa only [if_pos h] using hκ.isProbabilityMeasure c
    · simpa only [if_neg h] using hη.isProbabilityMeasure c⟩

/-- Case analysis on an `Option`, as produced by an early `return` inside an `rdo` `for` loop. -/
theorem optionCasesOn {G : γ → Measure α} {H : γ → β → Measure α}
    (hG : IsMarkov G) (hH : IsMarkov fun p : γ × β => H p.1 p.2) :
    IsMarkov fun q : γ × Option β =>
      Option.casesOn (motive := fun _ => Measure α) q.2 (G q.1) (H q.1) := by
  refine ⟨Measurable.optionCasesOn hG.measurable hH.measurable, ?_⟩
  rintro ⟨c, o⟩
  cases o with
  | none => exact hG.isProbabilityMeasure c
  | some b => exact hH.isProbabilityMeasure (c, b)

/-- The form of `IsMarkov.optionCasesOn` matching the `match` an early `return` produces: the
scrutinee may be any measurable function of the parameter. -/
theorem optionCases {o : γ → Option β} {G : γ → Measure α} {H : γ → β → Measure α}
    (hG : IsMarkov G) (hH : IsMarkov fun p : γ × β => H p.1 p.2)
    (ho : Measurable o := by fun_prop) :
    IsMarkov fun c => match o c with
      | some b => H c b
      | none => G c := by
  refine IsMarkov.congr ?_
    ((optionCasesOn hG hH).comp (g := fun c => (c, o c)) (measurable_id.prodMk ho))
  intro c
  cases o c <;> simp

/-- Case analysis on a `ForInStep`, as produced by the body of an `rdo` `for` loop. -/
theorem forInStepCasesOn {G H : γ → β → Measure α}
    (hG : IsMarkov fun p : γ × β => G p.1 p.2) (hH : IsMarkov fun p : γ × β => H p.1 p.2) :
    IsMarkov fun q : γ × ForInStep β =>
      ForInStep.casesOn (motive := fun _ => Measure α) q.2 (G q.1) (H q.1) := by
  refine ⟨Measurable.forInStepCasesOn hG.measurable hH.measurable, ?_⟩
  rintro ⟨c, s⟩
  cases s with
  | done b => exact hG.isProbabilityMeasure (c, b)
  | yield b => exact hH.isProbabilityMeasure (c, b)

end IsMarkov

/-! ### Direct `IsProbabilityMeasure` corollaries

These are the specialisations of the lemmas above to closed programs; they are what one applies
by hand when not using the `is_markov` tactic. -/

instance isProbabilityMeasure_mPure (a : α) : IsProbabilityMeasure (mPure a : Measure α) :=
  isMarkov_mPure.isProbabilityMeasure a

theorem isProbabilityMeasure_mBind {μ : Measure α} [IsProbabilityMeasure μ] {η : α → Measure β}
    (hη : IsMarkov η) : IsProbabilityMeasure (μ >>=ₘ η) :=
  isProbabilityMeasure_of_isMarkov <|
    (IsMarkov.const (γ := PUnit.{u + 1}) μ).mBind (hη.comp measurable_snd)

theorem isProbabilityMeasure_mMap {μ : Measure α} [IsProbabilityMeasure μ] {g : α → β}
    (hg : Measurable g := by fun_prop) : IsProbabilityMeasure (g <$>ₘ μ : Measure β) :=
  isProbabilityMeasure_of_isMarkov <|
    (IsMarkov.const (γ := PUnit.{u + 1}) μ).mMap (g := fun _ => g) (by fun_prop)

/-! ### `for` loops

An `rdo` `for` loop over a collection `xs` elaborates to `MeasurableSpaceForIn.forIn xs b f`. The
classes below record that such a loop is a Markov kernel whenever its body is; instances are
provided for the collections supported by `rdo` (`List`, `Array` and `Vector`).

The ambient parameter `γ` is required to live in the same universe as the loop state. This is not
a restriction in practice: every type occurring in an `rdo` block lives in that universe (use
`PUnit` for a closed program). -/

section ForIn

/-- Collections `ρ` whose `rdo` loops `for h : x in xs` preserve the Markov property.

The field says: if the initial state depends measurably on the parameter, and if the loop body is
a Markov kernel in (parameter, state) for every element of the collection, then so is the loop. -/
class IsMarkovForIn' (ρ : Type uρ) (ι : Type uα) (d : Membership ι ρ)
    [MeasurableSpaceForIn' Measure.{u} ρ ι d] : Prop where
  /-- `rdo`'s `for h : x in xs` preserves the Markov property. -/
  isMarkov_forIn' {γ β : Type u} [MeasurableSpace γ] [MeasurableSpace β]
      (xs : ρ) (b : γ → β) (hb : Measurable b)
      (f : γ → (a : ι) → a ∈ xs → β → Measure (ForInStep β))
      (hf : ∀ (a : ι) (h : a ∈ xs), IsMarkov fun p : γ × β => f p.1 a h p.2) :
    IsMarkov fun c => MeasurableSpaceForIn'.forIn' (m := Measure) xs (b c) (f c)

/-- Collections `ρ` whose `rdo` loops `for x in xs` preserve the Markov property. -/
class IsMarkovForIn (ρ : Type uρ) (ι : Type uα)
    [MeasurableSpaceForIn Measure.{u} ρ ι] : Prop where
  /-- `rdo`'s `for x in xs` preserves the Markov property. -/
  isMarkov_forIn {γ β : Type u} [MeasurableSpace γ] [MeasurableSpace β]
      (xs : ρ) (b : γ → β) (hb : Measurable b)
      (f : γ → ι → β → Measure (ForInStep β))
      (hf : ∀ a : ι, IsMarkov fun p : γ × β => f p.1 a p.2) :
    IsMarkov fun c => MeasurableSpaceForIn.forIn (m := Measure) xs (b c) (f c)

instance (priority := 500) instIsMarkovForInOfForIn' {ρ : Type uρ} {ι : Type uα}
    {d : Membership ι ρ} [MeasurableSpaceForIn' Measure.{u} ρ ι d] [IsMarkovForIn' ρ ι d] :
    IsMarkovForIn ρ ι where
  isMarkov_forIn xs b hb _f hf := IsMarkovForIn'.isMarkov_forIn' xs b hb _ fun a _ => hf a

variable {ρ : Type uρ} {ι : Type uα} {γ' β' : Type u} [MeasurableSpace γ'] [MeasurableSpace β']

/-- `rdo`'s `for x in xs` preserves the Markov property. This is the form the `is_markov` tactic
applies. -/
theorem IsMarkov.forIn [MeasurableSpaceForIn Measure.{u} ρ ι] [IsMarkovForIn ρ ι]
    {xs : ρ} {b : γ' → β'} {f : γ' → ι → β' → Measure (ForInStep β')}
    (hf : ∀ a : ι, IsMarkov fun p : γ' × β' => f p.1 a p.2)
    (hb : Measurable b := by fun_prop) :
    IsMarkov fun c => MeasurableSpaceForIn.forIn (m := Measure) xs (b c) (f c) :=
  IsMarkovForIn.isMarkov_forIn xs b hb f hf

/-- `rdo`'s `for h : x in xs` preserves the Markov property. -/
theorem IsMarkov.forIn' {d : Membership ι ρ} [MeasurableSpaceForIn' Measure.{u} ρ ι d]
    [IsMarkovForIn' ρ ι d] {xs : ρ} {b : γ' → β'}
    {f : γ' → (a : ι) → a ∈ xs → β' → Measure (ForInStep β')}
    (hf : ∀ (a : ι) (h : a ∈ xs), IsMarkov fun p : γ' × β' => f p.1 a h p.2)
    (hb : Measurable b := by fun_prop) :
    IsMarkov fun c => MeasurableSpaceForIn'.forIn' (m := Measure) xs (b c) (f c) :=
  IsMarkovForIn'.isMarkov_forIn' xs b hb f hf

end ForIn

/-! #### `List` -/

namespace List

variable {ι : Type uα} {γ β : Type u} [MeasurableSpace γ] [MeasurableSpace β]

private theorem isMarkov_measurableSpaceForIn'_loop {as : List ι}
    {f : γ → (a : ι) → a ∈ as → β → Measure (ForInStep β)}
    (hf : ∀ (a : ι) (h : a ∈ as), IsMarkov fun p : γ × β => f p.1 a h p.2) :
    ∀ (as' : List ι) (h : ∃ bs, bs ++ as' = as),
      IsMarkov fun p : γ × β => List.measurableSpaceForIn'.loop as (f p.1) as' p.2 h := by
  intro as'
  induction as' with
  | nil =>
    intro h
    simpa only [List.measurableSpaceForIn'.loop.eq_1] using
      IsMarkov.mPure_comp (g := fun p : γ × β => p.2) measurable_snd
  | cons a as' ih =>
    intro h
    obtain ⟨bs, rfl⟩ := h
    have h' : ∃ bs', bs' ++ as' = bs ++ a :: as' := ⟨bs ++ [a], by simp⟩
    simp only [List.measurableSpaceForIn'.loop.eq_2]
    refine IsMarkov.mBind (hf a _) (IsMarkov.congr ?_ (IsMarkov.forInStepCasesOn
      (G := fun (_ : γ × β) (b : β) => (mPure b : Measure β))
      (H := fun (p : γ × β) (b : β) =>
        List.measurableSpaceForIn'.loop (bs ++ a :: as') (f p.1) as' b h')
      (IsMarkov.mPure_comp measurable_snd)
      ((ih h').comp (g := fun r : (γ × β) × β => (r.1.1, r.2)) (by fun_prop))))
    rintro ⟨q, s⟩
    cases s <;> rfl

/-- An `rdo` `for` loop over a `List` is a Markov kernel as soon as its body is. -/
theorem isMarkov_measurableSpaceForIn' (as : List ι) {b : γ → β}
    {f : γ → (a : ι) → a ∈ as → β → Measure (ForInStep β)}
    (hf : ∀ (a : ι) (h : a ∈ as), IsMarkov fun p : γ × β => f p.1 a h p.2)
    (hb : Measurable b := by fun_prop) :
    IsMarkov fun c => List.measurableSpaceForIn' as (b c) (f c) := by
  have h := isMarkov_measurableSpaceForIn'_loop hf as ⟨[], rfl⟩
  simpa only [List.measurableSpaceForIn'.eq_def] using
    h.comp (g := fun c : γ => (c, b c)) (measurable_id.prodMk hb)

instance : IsMarkovForIn' (List ι) ι inferInstance where
  isMarkov_forIn' xs _ hb _ hf := isMarkov_measurableSpaceForIn' xs hf hb

end List

/-! #### `Array` and `Vector` -/

namespace Array

variable {ι γ β : Type u} [MeasurableSpace γ] [MeasurableSpace β]

private theorem isMarkov_measurableSpaceForIn'_loop {as : Array ι}
    {f : γ → (a : ι) → a ∈ as → β → Measure (ForInStep β)}
    (hf : ∀ (a : ι) (h : a ∈ as), IsMarkov fun p : γ × β => f p.1 a h p.2) :
    ∀ (i : ℕ) (h : i ≤ as.size),
      IsMarkov fun p : γ × β => Array.measurableSpaceForIn'.loop as (f p.1) i h p.2 := by
  intro i
  induction i with
  | zero =>
    intro h
    simpa only [Array.measurableSpaceForIn'.loop.eq_1] using
      IsMarkov.mPure_comp (g := fun p : γ × β => p.2) measurable_snd
  | succ i ih =>
    intro h
    have hi : i ≤ as.size := Nat.le_of_succ_le h
    simp only [Array.measurableSpaceForIn'.loop.eq_2]
    refine IsMarkov.mBind (hf _ _) (IsMarkov.congr ?_ (IsMarkov.forInStepCasesOn
      (G := fun (_ : γ × β) (b : β) => (mPure b : Measure β))
      (H := fun (p : γ × β) (b : β) => Array.measurableSpaceForIn'.loop as (f p.1) i hi b)
      (IsMarkov.mPure_comp measurable_snd)
      ((ih hi).comp (g := fun r : (γ × β) × β => (r.1.1, r.2)) (by fun_prop))))
    rintro ⟨q, s⟩
    cases s <;> rfl

/-- An `rdo` `for` loop over an `Array` is a Markov kernel as soon as its body is. -/
theorem isMarkov_measurableSpaceForIn' (as : Array ι) {b : γ → β}
    {f : γ → (a : ι) → a ∈ as → β → Measure (ForInStep β)}
    (hf : ∀ (a : ι) (h : a ∈ as), IsMarkov fun p : γ × β => f p.1 a h p.2)
    (hb : Measurable b := by fun_prop) :
    IsMarkov fun c => Array.measurableSpaceForIn' as (b c) (f c) := by
  have h := isMarkov_measurableSpaceForIn'_loop hf as.size le_rfl
  simpa only [Array.measurableSpaceForIn'.eq_def] using
    h.comp (g := fun c : γ => (c, b c)) (measurable_id.prodMk hb)

instance : IsMarkovForIn' (Array ι) ι inferInstance where
  isMarkov_forIn' xs _ hb _ hf := isMarkov_measurableSpaceForIn' xs hf hb

instance {n : ℕ} : IsMarkovForIn' (Vector ι n) ι inferInstance where
  isMarkov_forIn' xs _ hb _ hf :=
    isMarkov_measurableSpaceForIn' xs.toArray (fun a h => hf a (by simpa using h)) hb

end Array

/-! #### Unrolling a loop over a `List`

The equations below give the `rdo` `for` loop over a list its expected recursive behaviour. They
are stated for an arbitrary `MeasurableSpaceMonad`, and are what allows one to reason about a loop
whose *collection* is not fixed. -/

section Unroll

universe u' v'

variable {m : (α : Type u') → [MeasurableSpace α] → Type v'} [MeasurableSpaceMonad m]
  {ι : Type*} {β' : Type u'} [MeasurableSpace β']

/-- The denotation of an `rdo` `for` loop over a list, as a plain structural recursion. -/
private def listLoop (g : ι → β' → m (ForInStep β')) : List ι → β' → m β'
  | [], b => mPure b
  | a :: l, b => g a b >>=ₘ fun step =>
      ForInStep.casesOn (motive := fun _ => m β') step mPure fun b' => listLoop g l b'

/-- The reference implementation of `forIn'` does not depend on the ambient list `as`, only on the
suffix being traversed, as long as the body ignores the membership proofs. -/
private theorem loop_eq_listLoop (g : ι → β' → m (ForInStep β')) :
    ∀ (l : List ι) (b : β') (as : List ι) (f : (a : ι) → a ∈ as → β' → m (ForInStep β'))
      (_hf : ∀ a h b, f a h b = g a b) (h : ∃ bs, bs ++ l = as),
      List.measurableSpaceForIn'.loop as f l b h = listLoop g l b := by
  intro l
  induction l with
  | nil =>
    intro b as f _hf h
    rw [List.measurableSpaceForIn'.loop.eq_1]
    rfl
  | cons a l ih =>
    intro b as f hf h
    rw [List.measurableSpaceForIn'.loop.eq_2, hf]
    change _ = g a b >>=ₘ _
    refine MeasurableSpaceBind.bind_congr fun step => ?_
    cases step with
    | done b' => rfl
    | yield b' => exact ih b' as f hf _

private theorem forIn_eq_listLoop (l : List ι) (b : β') (g : ι → β' → m (ForInStep β')) :
    MeasurableSpaceForIn.forIn (m := m) l b g = listLoop g l b :=
  loop_eq_listLoop g l b l _ (fun _ _ _ => rfl) ⟨[], rfl⟩

/-- An `rdo` `for` loop over the empty list returns its initial state. -/
theorem forIn_nil (b : β') (g : ι → β' → m (ForInStep β')) :
    MeasurableSpaceForIn.forIn (m := m) ([] : List ι) b g = mPure b :=
  forIn_eq_listLoop _ _ _

/-- Unrolling one step of an `rdo` `for` loop over a list. -/
theorem forIn_cons (a : ι) (l : List ι) (b : β') (g : ι → β' → m (ForInStep β')) :
    MeasurableSpaceForIn.forIn (m := m) (a :: l) b g
      = g a b >>=ₘ fun step => ForInStep.casesOn (motive := fun _ => m β') step mPure
          fun b' => MeasurableSpaceForIn.forIn (m := m) l b' g := by
  rw [forIn_eq_listLoop]
  refine MeasurableSpaceBind.bind_congr fun step => ?_
  cases step with
  | done b' => rfl
  | yield b' => exact (forIn_eq_listLoop l b' g).symm

section ArrayUnroll

variable {ιa : Type u'} [MeasurableSpace ιa]

omit [MeasurableSpace ιa] in
private theorem arrayLoop_eq_listLoop (g : ιa → β' → m (ForInStep β')) (as : Array ιa)
    (f : (a : ιa) → a ∈ as → β' → m (ForInStep β')) (hf : ∀ a h b, f a h b = g a b) :
    ∀ (i : ℕ) (h : i ≤ as.size) (b : β'),
      Array.measurableSpaceForIn'.loop as f i h b
        = listLoop g (as.toList.drop (as.size - i)) b := by
  intro i
  induction i with
  | zero =>
    intro h b
    have hnil : List.drop (as.size - 0) as.toList = [] := by simp
    rw [Array.measurableSpaceForIn'.loop.eq_1, hnil]
    rfl
  | succ i ih =>
    intro h b
    have hi : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
    have hk : as.size - (i + 1) < as.toList.length := by
      simp only [Array.length_toList]; omega
    rw [Array.measurableSpaceForIn'.loop.eq_2, hf, List.drop_eq_getElem_cons hk]
    have hidx : as.toList[as.size - (i + 1)] = as[as.size - 1 - i] := by
      rw [Array.getElem_toList]; congr 1; omega
    have hnext : as.size - (i + 1) + 1 = as.size - i := by omega
    rw [hidx, hnext]
    change _ = g as[as.size - 1 - i] b >>=ₘ _
    refine MeasurableSpaceBind.bind_congr fun step => ?_
    cases step with
    | done b' => rfl
    | yield b' => exact ih (Nat.le_of_succ_le h) b'

omit [MeasurableSpace ιa] in
/-- An `rdo` `for` loop over an `Array` is the loop over its underlying list. -/
theorem forIn_array (as : Array ιa) (b : β') (g : ιa → β' → m (ForInStep β')) :
    MeasurableSpaceForIn.forIn (m := m) as b g
      = MeasurableSpaceForIn.forIn (m := m) as.toList b g := by
  rw [forIn_eq_listLoop]
  change Array.measurableSpaceForIn'.loop as _ as.size _ b = _
  rw [arrayLoop_eq_listLoop g as _ (fun _ _ _ => rfl)]
  simp

end ArrayUnroll

end Unroll

/-! #### Loops whose collection depends on the parameter

`RDo.IsMarkov.forIn` covers a loop over a *fixed* collection. When the collection is itself the
parameter — as in `IsMarkov (fun xs : Array ℝ => rdo ... for a in xs ...)` — one needs in addition
that the body is measurable in the element being traversed, which is what `hg` asks for below. -/

section VaryingCollection

variable {ι : Type*} [MeasurableSpace ι]

/-- A family of measures indexed by a list is Markov as soon as it is Markov on every stratum of
lists of a fixed length. -/
theorem IsMarkov.of_prodList {δ : Type*} [MeasurableSpace δ] {κ : δ × List ι → Measure α}
    (h : ∀ n, IsMarkov fun q : δ × (Fin n → ι) => κ (q.1, List.ofFn q.2)) : IsMarkov κ := by
  refine ⟨measurable_of_prodList fun n => (h n).measurable, ?_⟩
  rintro ⟨d, l⟩
  simpa only [List.ofFn_get] using (h l.length).isProbabilityMeasure (d, l.get)

/-- An `rdo` `for` loop over a list that depends measurably on the parameter. -/
theorem IsMarkov.forInList {xs : γ → List ι} {b : γ → β}
    {g : γ → ι → β → Measure (ForInStep β)}
    (hg : IsMarkov fun p : (γ × ι) × β => g p.1.1 p.1.2 p.2)
    (hxs : Measurable xs := by fun_prop) (hb : Measurable b := by fun_prop) :
    IsMarkov fun c => MeasurableSpaceForIn.forIn (m := Measure) (xs c) (b c) (g c) := by
  have key : IsMarkov fun q : (γ × β) × List ι =>
      MeasurableSpaceForIn.forIn (m := Measure) q.2 q.1.2 (g q.1.1) := by
    refine IsMarkov.of_prodList fun n => ?_
    induction n with
    | zero =>
      simp only [List.ofFn_zero, forIn_nil]
      exact IsMarkov.mPure_comp (by fun_prop)
    | succ n ih =>
      simp only [List.ofFn_succ, forIn_cons]
      refine IsMarkov.mBind
        (hg.comp (g := fun q : (γ × β) × (Fin (n + 1) → ι) => ((q.1.1, q.2 0), q.1.2))
          (by fun_prop)) ?_
      exact IsMarkov.forInStepCasesOn
        (G := fun (_ : (γ × β) × (Fin (n + 1) → ι)) (b' : β) => (mPure b' : Measure β))
        (H := fun (q : (γ × β) × (Fin (n + 1) → ι)) (b' : β) =>
          MeasurableSpaceForIn.forIn (m := Measure) (List.ofFn fun i => q.2 i.succ) b' (g q.1.1))
        (IsMarkov.mPure_comp measurable_snd)
        (ih.comp (g := fun r : ((γ × β) × (Fin (n + 1) → ι)) × β =>
          ((r.1.1.1, r.2), fun i => r.1.2 i.succ)) (by fun_prop))
  exact key.comp (g := fun c => ((c, b c), xs c)) (by fun_prop)

/-- An `rdo` `for` loop over an array that depends measurably on the parameter. -/
theorem IsMarkov.forInArray {ι : Type u} [MeasurableSpace ι] {xs : γ → Array ι} {b : γ → β}
    {g : γ → ι → β → Measure (ForInStep β)}
    (hg : IsMarkov fun p : (γ × ι) × β => g p.1.1 p.1.2 p.2)
    (hxs : Measurable xs := by fun_prop) (hb : Measurable b := by fun_prop) :
    IsMarkov fun c => MeasurableSpaceForIn.forIn (m := Measure) (xs c) (b c) (g c) := by
  simp only [forIn_array]
  exact IsMarkov.forInList hg (measurable_toList.comp hxs) hb

end VaryingCollection

/-! ### The `is_markov` tactic -/

/--
`is_markov` proves that an `rdo` program in the `MeasureTheory.Measure` monad is a probability
measure (goal `IsProbabilityMeasure μ`) or a Markov kernel (goal `RDo.IsMarkov κ`).

It walks through the structure of the program — `mPure`, `>>=ₘ`, `<$>ₘ`, `if`, `for` loops and
the `Option` produced by an early `return` — using the lemmas of this file, and discharges the
measurability side conditions with `fun_prop` (falling back on `measurability` for `MeasurableSet`
goals). Facts `IsMarkov κ` about the kernels appearing in the program are picked up from the local
context or from instance search, possibly up to a measurable reparametrisation.

Typical use, on a program defined by `def prog : Measure α := rdo ...`:
```
example : IsProbabilityMeasure prog := by unfold prog; is_markov
```

When a measurability side condition is out of reach of `fun_prop`, the tactic stops and leaves
precisely that goal, which can then be proved by hand.
-/
syntax (name := isMarkovTac) "is_markov" : tactic

macro_rules
  | `(tactic| is_markov) => `(tactic|
      repeat' first
        | assumption
        | infer_instance
        | fun_prop
        | (unfold autoParam; first | fun_prop | measurability)
        | unfold autoParam
        | (with_reducible apply RDo.IsMarkov.mPure_comp)
        | (with_reducible apply RDo.IsMarkov.mBind)
        | (with_reducible apply RDo.IsMarkov.mMap)
        | (with_reducible apply RDo.IsMarkov.forIn)
        | (with_reducible apply RDo.IsMarkov.forIn')
        | (with_reducible apply RDo.IsMarkov.forInList)
        | (with_reducible apply RDo.IsMarkov.forInArray)
        | (with_reducible apply RDo.IsMarkov.ite)
        | (with_reducible apply RDo.isProbabilityMeasure_of_isMarkov)
        | apply RDo.IsMarkov.optionCases
        | (with_reducible refine RDo.IsMarkov.comp ?_ ?_ <;>
            first | assumption | infer_instance | fun_prop)
        | (intro _; intros;
            first | (change RDo.IsMarkov _) | (change IsProbabilityMeasure _))
        | measurability)

end RDo
