/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.Bind
public import LeanMachineLearning.RDo.ForInStep
public import LeanMachineLearning.RDo.ForInInstances

/-!
# `IsMarkov` is stable under an `rdo` `for` loop over a `List`

`for a in xs rdo body` elaborates to `MeasurableSpaceForIn.forIn xs b f`, which for a `List`
unfolds to the reference implementation `List.measurableSpaceForIn'`. The latter is a structural
recursion on the suffix of `xs` that remains to be traversed, so the proof is an induction on that
suffix: the empty suffix gives `return b`, and a suffix `a :: as'` gives one `mBind` of the body
followed by a case analysis on the resulting `ForInStep`.

## Main statements

* `RDo.IsMarkov.forInList`: an `rdo` `for` loop over a fixed list is a Markov kernel as soon as
  its body is, for each element of the list.
-/

@[expose] public section

open MeasureTheory
open MeasurableSpacePure MeasurableSpaceBind

namespace RDo

universe u

variable {ι : Type*} {γ : Type*} {β : Type u} [MeasurableSpace γ] [MeasurableSpace β]

/-- The induction underlying `RDo.IsMarkov.forInList`, on the suffix `as'` still to be traversed.

`as` is the whole list, fixed throughout; `h` witnesses that `as'` is a suffix of `as`, and is
what lets the body receive a membership proof. Being a proof, it plays no role in the statement:
two instances of `loop` differing only by it are definitionally equal. -/
private theorem isMarkov_loop {as : List ι}
    {f : γ → (a : ι) → a ∈ as → β → Measure (ForInStep β)}
    (hf : ∀ (a : ι) (h : a ∈ as), IsMarkov fun p : γ × β => f p.1 a h p.2) :
    ∀ (as' : List ι) (h : ∃ bs, bs ++ as' = as),
      IsMarkov fun p : γ × β => List.measurableSpaceForIn'.loop as (f p.1) as' p.2 h := by
  intro as'
  induction as' with
  | nil =>
    -- Empty suffix: the loop is `return b`, where `b` is the state component of the parameter.
    intro h
    simpa only [List.measurableSpaceForIn'.loop.eq_1] using
      IsMarkov.mPure_comp (g := fun p : γ × β => p.2) measurable_snd
  | cons a as' ih =>
    intro h
    obtain ⟨bs, rfl⟩ := h
    have h' : ∃ bs', bs' ++ as' = bs ++ a :: as' := ⟨bs ++ [a], by simp⟩
    -- One step: `f a b >>=ₘ fun step => match step with | done b => return b | yield b => loop b`.
    simp only [List.measurableSpaceForIn'.loop.eq_2]
    refine IsMarkov.mBind (hf a _) (IsMarkov.congr ?_ (IsMarkov.forInStepCasesOn
      -- `done b`: the loop stops and returns `b`.
      (G := fun (_ : γ × β) (b : β) => (mPure b : Measure β))
      -- `yield b`: the loop goes on over the shorter suffix, which is the induction hypothesis.
      (H := fun (p : γ × β) (b : β) =>
        List.measurableSpaceForIn'.loop (bs ++ a :: as') (f p.1) as' b h')
      (IsMarkov.mPure_comp measurable_snd)
      ((ih h').comp (g := fun r : (γ × β) × β => (r.1.1, r.2)) (by fun_prop))))
    -- The elaborator produced a `match`; it agrees with `ForInStep.casesOn` on each constructor.
    rintro ⟨q, s⟩
    cases s <;> rfl

/-- An `rdo` `for` loop over the fixed list `xs` is a Markov kernel as soon as its body is one for
each element of `xs`, and the initial state depends measurably on the parameter.

Note that `hf` quantifies over the elements *from the outside*: each `a` is frozen, so no
measurable structure is needed on `ι`. -/
theorem IsMarkov.forInList (xs : List ι) {b : γ → β} {f : γ → ι → β → Measure (ForInStep β)}
    (hf : ∀ a : ι, IsMarkov fun p : γ × β => f p.1 a p.2)
    (hb : Measurable b := by fun_prop) :
    IsMarkov fun c => MeasurableSpaceForIn.forIn (m := Measure) xs (b c) (f c) :=
  (isMarkov_loop (as := xs) (f := fun c a _ s => f c a s) (fun a _ => hf a) xs ⟨[], rfl⟩).comp
    (g := fun c : γ => (c, b c)) (measurable_id.prodMk hb)

end RDo
