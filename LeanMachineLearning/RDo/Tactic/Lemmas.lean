/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.Monad.Instances
public import LeanMachineLearning.RDo.Monad.ForInInstances
public import LeanMachineLearning.RDo.Tactic.ForInStep
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!

# Markov property of `rdo` programs

This file contains lemmas about the Markov property of `rdo` programs, i.e. measurability and
probability measure conditions. The purpose of this file is to propagate the `IsMarkov` property
through the constructs of the `rdo` language, allowing the `is_markov` tactic to automatically
verify that a given `rdo` program is Markovian or to reduce the proof of the Markov property of a
complex program to the Markov property/measurability of its underlying mathematical components.

## Main results

* `mPure_comp`: `rdo`'s `return e`, for an expression `e` depending measurably on the parameter, is
  Markovian.
* `measurable_bind`: Binding a Markov kernel `κ` with a family `η` that is jointly measurable in
the parameter and in the bound variable is measurable in the parameter.
* `mBind`: Binding a Markov kernel `κ` with a family `η` that is Markovian in the parameter and the
bound variable is Markovian in the parameter.
* `comp`: Composing a Markov kernel `κ` with a measurable function `g` is Markovian in the
parameter.
* `ite`: A conditional `rdo` program that chooses between two Markov kernels `κ` and `η` based on a
measurable predicate `p` is Markovian in the parameter.
* `dite`: A dependent conditional `rdo` program that chooses between two Markov kernels `κ` and `η`
based on a measurable predicate `p` is Markovian in the parameter.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open MeasurableSpacePure

namespace IsMarkov

universe u

variable {γ γ' : Type*} [MeasurableSpace γ] [MeasurableSpace γ'] {α β : Type u}
  [MeasurableSpace α] [MeasurableSpace β]

lemma mPure_comp {g : γ → α} (hg : Measurable g) : IsMarkov fun c ↦ (mPure (g c) : Measure α) := by
  refine ⟨Measure.measurable_dirac.comp hg, ?_⟩
  · intro c
    simp only [mPure_def]
    infer_instance

private lemma measurable_bind {κ : γ → Measure α} (hκ : IsMarkov κ)
    {η : γ → α → Measure β} (hη : Measurable (uncurry η)) :
    Measurable fun c ↦ (κ c).bind (η c) := by
  let κ' : Kernel γ α := hκ.toKernel
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have hηc : ∀ c, Measurable (η c) := by
    intro c
    fun_prop
  simp_rw [Measure.bind_apply hs (hηc _).aemeasurable]
  exact Measurable.lintegral_kernel_prod_right (κ := κ') ((Measure.measurable_coe hs).comp hη)

lemma mBind {κ : γ → Measure α} (hκ : IsMarkov κ) {η : γ → α → Measure β}
    (hη : IsMarkov fun p : γ × α ↦ η p.1 p.2) : IsMarkov fun c ↦ κ c >>=ₘ η c := by
  have hη' : Measurable (uncurry η) := hη.measurable
  simp only [mBind_def]
  refine ⟨measurable_bind hκ hη', fun c ↦ ?_⟩
  · have := hκ.isProbabilityMeasure c
    refine isProbabilityMeasure_bind ?_ ?_
    · exact Measurable.aemeasurable (by fun_prop)
    · refine Filter.Eventually.of_forall fun a ↦ ?_
      exact hη.isProbabilityMeasure (c, a)

lemma comp {κ : γ → Measure α} (hκ : IsMarkov κ) {g : γ' → γ} (hg : Measurable g) :
    IsMarkov fun c ↦ κ (g c) := ⟨hκ.measurable.comp hg, fun _ ↦ hκ.isProbabilityMeasure _⟩

lemma ite {p : γ → Prop} [DecidablePred p] (hp : Measurable p)
    {κ η : γ → Measure α} (hκ : IsMarkov κ) (hη : IsMarkov η) :
    IsMarkov fun c ↦ if p c then κ c else η c := by
  refine ⟨hκ.measurable.ite hp.setOf hη.measurable, fun c ↦ ?_⟩
  by_cases h : p c
  · simpa [h] using hκ.isProbabilityMeasure c
  · simpa [h] using hη.isProbabilityMeasure c

lemma dite {p : γ → Prop} [inst : DecidablePred p] (hp : Measurable p)
    {κ : {c // p c} → Measure α} (hκ : IsMarkov κ)
    {η : {c // ¬ p c} → Measure α} (hη : IsMarkov η) :
    IsMarkov fun c ↦ if h : p c then κ ⟨c, h⟩ else η ⟨c, h⟩ := by
  refine ⟨.dite (s := {c | p c}) hκ.measurable hη.measurable hp.setOf, fun c ↦ ?_⟩
  by_cases h : p c
  · simpa [h] using hκ.isProbabilityMeasure _
  · simpa [h] using hη.isProbabilityMeasure _

omit [MeasurableSpace γ] in
private lemma list_loop {as : List γ}
    {f : α → (a : γ) → a ∈ as → γ' → Measure (ForInStep γ')}
    (hf : ∀ a h, IsMarkov fun p : α × γ' => f p.1 a h p.2) :
    ∀ as' (h : ∃ bs, bs ++ as' = as),
      IsMarkov fun p : α × γ' ↦ List.measurableSpaceForIn'.loop as (f p.1) as' p.2 h := by
  intro as'
  induction as' with
  | nil =>
    intro h
    simpa only [List.measurableSpaceForIn'.loop.eq_1] using
      IsMarkov.mPure_comp (g := fun p : α × γ' => p.2) measurable_snd
  | cons a as' ih =>
    intro h
    obtain ⟨bs, rfl⟩ := h
    have h' : ∃ bs', bs' ++ as' = bs ++ a :: as' := ⟨bs ++ [a], by simp⟩
    simp only [List.measurableSpaceForIn'.loop.eq_2]
    refine IsMarkov.mBind ?_ ?_
    · exact hf a List.mem_append_cons_self
    · have := IsMarkov.forInStepCasesOn
        (done := fun (_ : α × γ') (b : γ') ↦ (mPure b : Measure γ'))
        (yield := fun (p : α × γ') (b : γ') ↦
          List.measurableSpaceForIn'.loop (bs ++ a :: as') (f p.1) as' b h')
        (IsMarkov.mPure_comp measurable_snd)
        ((ih h').comp (g := fun r : (α × γ') × γ' ↦ (r.1.1, r.2)) (by fun_prop))
      refine IsMarkov.congr (hη := this) fun (q, s) ↦ ?_
      cases s <;> rfl

omit [MeasurableSpace γ] in
lemma forInList {as : List γ} {b : α → γ'} {f : α → γ → γ' → Measure (ForInStep γ')}
    (hb : Measurable b) (hf : ∀ a, IsMarkov fun p : α × γ' => f p.1 a p.2) :
    IsMarkov fun c => MeasurableSpaceForIn.forIn (m := Measure) as (b c) (f c) :=
  (list_loop (f := fun c a _ s ↦ f c a s) (fun a _ ↦ hf a) as ⟨[], rfl⟩).comp
    (g := fun c ↦ (c, b c)) (measurable_id.prodMk hb)


end IsMarkov
