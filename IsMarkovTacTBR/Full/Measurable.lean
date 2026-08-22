/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.ForInInstances
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.Data.List.OfFn

/-!
# Measurability of the data types used by `rdo` programs

`rdo` programs manipulate the loop-control type `ForInStep` and the collection types `List`,
`Array` and `Vector`, all of which carry a `MeasurableSpace` instance defined in
`LeanMachineLearning.RDo.MeasurableSpaceMonad` and `LeanMachineLearning.RDo.ForInInstances`.
This file provides the measurability lemmas for the basic operations on those types, so that
`fun_prop` can discharge the side conditions arising in proofs about `rdo` programs.

## Main statements

* `RDo.Measurable.forInStepCasesOn`: case analysis on a `ForInStep` preserves measurability.
* `RDo.measurable_concat`, `RDo.measurable_cons`, `RDo.measurable_push`: appending an element to a
  `List` or an `Array` is measurable. These are what makes an accumulator such as
  `xs := xs.push b` usable inside an `rdo` loop.

The measurable structure of `List α` is the one transported from `Σ n, Fin n → α` along
`List.equivSigmaTuple`, so the σ-algebra is the countable coproduct over the length of the list.
Accordingly, the proofs below decompose a list-valued map along its length.
-/

@[expose] public section

open MeasureTheory Function Set

namespace ForInStep

variable {β : Type*}

/-- `s.isDone` is `true` exactly when the loop step `s` requests early termination. -/
def isDone : ForInStep β → Bool
  | .done _ => true
  | .yield _ => false

@[simp] lemma isDone_done (b : β) : (ForInStep.done b).isDone = true := rfl

@[simp] lemma isDone_yield (b : β) : (ForInStep.yield b).isDone = false := rfl

end ForInStep

/-- The σ-algebra on `Option α` making it the coproduct of `α` and a point: a set is measurable
exactly when its trace on `α` is. `rdo` needs it because an early `return` inside a loop stores
the returned value in an `Option`. -/
instance Option.instMeasurableSpace {α : Type*} [m : MeasurableSpace α] :
    MeasurableSpace (Option α) := m.map Option.some

namespace RDo

/-! ### `ForInStep` -/

section ForInStep

variable {γ δ β : Type*} [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace β]

@[fun_prop]
theorem measurable_yield : Measurable (ForInStep.yield : β → ForInStep β) := fun _ hs => hs.1

@[fun_prop]
theorem measurable_done : Measurable (ForInStep.done : β → ForInStep β) := fun _ hs => hs.2

@[fun_prop]
theorem measurable_run : Measurable (ForInStep.run : ForInStep β → β) := fun _ hs => ⟨hs, hs⟩

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

/-- Case analysis on a `ForInStep` preserves measurability. This is the key ingredient making
`rdo` `for` loops tractable: the σ-algebra of `ForInStep β` is the coproduct of two copies of the
σ-algebra of `β`. -/
theorem Measurable.forInStepCasesOn {G H : γ → β → δ}
    (hG : Measurable (uncurry G)) (hH : Measurable (uncurry H)) :
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

end ForInStep

/-! ### `Option` -/

section Option

variable {γ δ α : Type*} [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace α]

theorem measurableSet_option_iff {s : Set (Option α)} :
    MeasurableSet s ↔ MeasurableSet (Option.some ⁻¹' s) := Iff.rfl

@[fun_prop]
theorem measurable_some : Measurable (Option.some : α → Option α) := fun _ hs => hs

theorem measurableSet_none : MeasurableSet ({none} : Set (Option α)) := by
  rw [measurableSet_option_iff]
  convert MeasurableSet.empty using 1
  ext a
  simp

theorem measurableEmbedding_some : MeasurableEmbedding (Option.some : α → Option α) :=
  ⟨Option.some_injective α, measurable_some, fun s hs => by
    rw [measurableSet_option_iff]
    simpa only [Option.some_injective α |>.preimage_image] using hs⟩

/-- Case analysis on an `Option` preserves measurability. -/
theorem Measurable.optionCasesOn {G : γ → δ} {H : γ → α → δ}
    (hG : Measurable G) (hH : Measurable (uncurry H)) :
    Measurable fun q : γ × Option α =>
      Option.casesOn (motive := fun _ => δ) q.2 (G q.1) (H q.1) := by
  intro t ht
  have key : (fun q : γ × Option α =>
        Option.casesOn (motive := fun _ => δ) q.2 (G q.1) (H q.1)) ⁻¹' t
      = (G ⁻¹' t) ×ˢ ({none} : Set (Option α))
        ∪ (Prod.map id Option.some) '' (uncurry H ⁻¹' t) := by
    ext ⟨c, o⟩
    cases o with
    | none => simp [Prod.ext_iff]
    | some a => simp [Prod.ext_iff, uncurry]
  rw [key]
  exact ((hG ht).prod measurableSet_none).union
    ((MeasurableEmbedding.id.prodMap measurableEmbedding_some).measurableSet_image' (hH ht))

end Option

/-! ### Sigma types -/

section Sigma

variable {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]

theorem measurableSet_sigma_iff {s : Set (Sigma β)} :
    MeasurableSet s ↔ ∀ i, MeasurableSet (Sigma.mk i ⁻¹' s) :=
  MeasurableSpace.measurableSet_iInf

@[fun_prop]
theorem measurable_sigmaMk (i : ι) : Measurable (Sigma.mk i : β i → Sigma β) :=
  fun _ hs => measurableSet_sigma_iff.1 hs i

theorem measurableSet_image_sigmaMk {i : ι} {s : Set (β i)} (hs : MeasurableSet s) :
    MeasurableSet (Sigma.mk i '' s) := by
  classical
  refine measurableSet_sigma_iff.2 fun j => ?_
  by_cases h : j = i
  · subst h
    convert hs using 1
    ext x
    simp [sigma_mk_injective.eq_iff]
  · convert MeasurableSet.empty using 1
    ext x
    simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
    rintro y - hy
    exact h (congrArg Sigma.fst hy).symm

theorem measurableEmbedding_sigmaMk (i : ι) :
    MeasurableEmbedding (Sigma.mk i : β i → Sigma β) :=
  ⟨sigma_mk_injective, measurable_sigmaMk i, fun _ hs => measurableSet_image_sigmaMk hs⟩

/-- The index of a point of a sigma type is measurable, whatever σ-algebra the index type
carries: the fibres of `Sigma.fst` are unions of whole summands. -/
@[fun_prop]
theorem measurable_sigmaFst [MeasurableSpace ι] : Measurable (Sigma.fst : Sigma β → ι) := by
  intro s _
  refine measurableSet_sigma_iff.2 fun i => ?_
  by_cases h : i ∈ s
  · convert MeasurableSet.univ using 1; ext x; simp [h]
  · convert MeasurableSet.empty using 1; ext x; simp [h]

end Sigma

/-! ### `List` -/

section List

variable {X α : Type*} [MeasurableSpace X] [MeasurableSpace α]

theorem measurable_equivSigmaTuple :
    Measurable (List.equivSigmaTuple : List α → Σ n, Fin n → α) := fun _ hs => ⟨_, hs, rfl⟩

theorem measurable_equivSigmaTuple_symm :
    Measurable (List.equivSigmaTuple.symm : (Σ n, Fin n → α) → List α) := by
  rintro s ⟨t, ht, rfl⟩
  simpa only [Equiv.symm_preimage_preimage] using ht

/-- `List α` is measurably equivalent to the sigma type of tuples. -/
def listMeasurableEquivSigmaTuple : List α ≃ᵐ Σ n, Fin n → α :=
  ⟨List.equivSigmaTuple, measurable_equivSigmaTuple, measurable_equivSigmaTuple_symm⟩

@[fun_prop]
theorem measurable_length : Measurable (List.length : List α → ℕ) :=
  measurable_sigmaFst.comp measurable_equivSigmaTuple

/-- `List.ofFn` is a measurable embedding: its image is the (measurable) set of lists of the
corresponding length. -/
theorem measurableEmbedding_ofFn (n : ℕ) :
    MeasurableEmbedding (List.ofFn : (Fin n → α) → List α) :=
  (listMeasurableEquivSigmaTuple.symm.measurableEmbedding).comp (measurableEmbedding_sigmaMk n)

@[fun_prop]
theorem measurable_ofFn (n : ℕ) : Measurable (List.ofFn : (Fin n → α) → List α) :=
  (measurableEmbedding_ofFn n).measurable

@[fun_prop]
theorem measurable_finSnoc {n : ℕ} :
    Measurable fun q : (Fin n → α) × α => (Fin.snoc q.1 q.2 : Fin (n + 1) → α) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; fun_prop
  · simp only [Fin.snoc_castSucc]; fun_prop

@[fun_prop]
theorem measurable_finCons {n : ℕ} :
    Measurable fun q : α × (Fin n → α) => (Fin.cons q.1 q.2 : Fin (n + 1) → α) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; fun_prop
  · simp only [Fin.cons_succ]; fun_prop

omit [MeasurableSpace α] in
private theorem ofFn_append_singleton {n : ℕ} (v : Fin n → α) (a : α) :
    List.ofFn v ++ [a] = List.ofFn (Fin.snoc v a : Fin (n + 1) → α) := by
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

omit [MeasurableSpace α] in
private theorem ofFn_cons {n : ℕ} (a : α) (v : Fin n → α) :
    a :: List.ofFn v = List.ofFn (Fin.cons a v : Fin (n + 1) → α) := by
  rw [List.ofFn_succ]
  simp

/-- Appending an element at the end of a list is measurable. -/
@[fun_prop]
theorem measurable_concat : Measurable fun p : List α × α => p.1 ++ [p.2] := by
  intro t ht
  have key : (fun p : List α × α => p.1 ++ [p.2]) ⁻¹' t
      = ⋃ n : ℕ, (Prod.map (List.ofFn (n := n)) id) ''
          ((fun q : (Fin n → α) × α => List.ofFn q.1 ++ [q.2]) ⁻¹' t) := by
    ext ⟨l, a⟩
    simp only [mem_preimage, mem_iUnion, mem_image, Prod.exists, Prod.map_apply, id_eq,
      Prod.mk.injEq]
    constructor
    · exact fun h => ⟨l.length, l.get, a, by simpa using h, by simp, rfl⟩
    · rintro ⟨n, v, b, hv, rfl, rfl⟩
      exact hv
  rw [key]
  refine MeasurableSet.iUnion fun n => ?_
  have hφ : Measurable fun q : (Fin n → α) × α => List.ofFn q.1 ++ [q.2] := by
    simp only [ofFn_append_singleton]
    exact (measurable_ofFn (n + 1)).comp measurable_finSnoc
  exact ((measurableEmbedding_ofFn n).prodMap MeasurableEmbedding.id).measurableSet_image' (hφ ht)

/-- A map defined on `δ × List α` is measurable as soon as it is measurable on each stratum
`δ × (Fin n → α)` of the lists of a fixed length. This is the shape in which one reasons about a
program whose input is a list: the σ-algebra of `List α` is the countable coproduct of those
strata. -/
theorem measurable_of_prodList {δ Y : Type*} [MeasurableSpace δ] [MeasurableSpace Y]
    {g : δ × List α → Y}
    (h : ∀ n, Measurable fun q : δ × (Fin n → α) => g (q.1, List.ofFn q.2)) : Measurable g := by
  intro t ht
  have key : g ⁻¹' t = ⋃ n : ℕ, (Prod.map id (List.ofFn (n := n))) ''
      ((fun q : δ × (Fin n → α) => g (q.1, List.ofFn q.2)) ⁻¹' t) := by
    ext ⟨d, l⟩
    simp only [mem_preimage, mem_iUnion, mem_image, Prod.exists, Prod.map_apply, id_eq,
      Prod.mk.injEq]
    constructor
    · exact fun hl => ⟨l.length, d, l.get, by simpa using hl, rfl, by simp⟩
    · rintro ⟨n, d', v, hv, rfl, rfl⟩
      exact hv
  rw [key]
  exact MeasurableSet.iUnion fun n =>
    (MeasurableEmbedding.id.prodMap (measurableEmbedding_ofFn n)).measurableSet_image' (h n ht)

/-- Prepending an element to a list is measurable. -/
@[fun_prop]
theorem measurable_cons : Measurable fun p : α × List α => p.1 :: p.2 := by
  intro t ht
  have key : (fun p : α × List α => p.1 :: p.2) ⁻¹' t
      = ⋃ n : ℕ, (Prod.map id (List.ofFn (n := n))) ''
          ((fun q : α × (Fin n → α) => q.1 :: List.ofFn q.2) ⁻¹' t) := by
    ext ⟨a, l⟩
    simp only [mem_preimage, mem_iUnion, mem_image, Prod.exists, Prod.map_apply, id_eq,
      Prod.mk.injEq]
    constructor
    · exact fun h => ⟨l.length, a, l.get, by simpa using h, rfl, by simp⟩
    · rintro ⟨n, b, v, hv, rfl, rfl⟩
      exact hv
  rw [key]
  refine MeasurableSet.iUnion fun n => ?_
  have hφ : Measurable fun q : α × (Fin n → α) => q.1 :: List.ofFn q.2 := by
    simp only [ofFn_cons]
    exact (measurable_ofFn (n + 1)).comp measurable_finCons
  exact (MeasurableEmbedding.id.prodMap (measurableEmbedding_ofFn n)).measurableSet_image'
    (hφ ht)

end List

/-! ### `Array` and `Vector` -/

section Array

variable {α : Type*} [MeasurableSpace α]

@[fun_prop]
theorem measurable_toList : Measurable (Array.toList : Array α → List α) := fun _ hs => ⟨_, hs, rfl⟩

@[fun_prop]
theorem measurable_toArray : Measurable (List.toArray : List α → Array α) := by
  rintro s ⟨t, ht, rfl⟩
  have key : List.toArray ⁻¹' (Array.toList ⁻¹' t) = t := by ext l; simp
  rwa [key]

@[fun_prop]
theorem measurable_size : Measurable (Array.size : Array α → ℕ) :=
  measurable_length.comp measurable_toList

/-- Pushing an element at the end of an array is measurable. This is what makes the usual
`xs := xs.push b` accumulator of an `rdo` loop measurable. -/
@[fun_prop]
theorem measurable_push : Measurable fun p : Array α × α => p.1.push p.2 := by
  have key : (fun p : Array α × α => p.1.push p.2)
      = List.toArray ∘ (fun q : List α × α => q.1 ++ [q.2]) ∘ Prod.map Array.toList id := by
    funext p
    simp [Function.comp_def, ← Array.toList_push]
  rw [key]
  exact measurable_toArray.comp
    (measurable_concat.comp (measurable_toList.prodMap measurable_id))

end Array

end RDo
