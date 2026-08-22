/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.Tactic.Lemmas
public meta import Lean.Elab.Tactic.Basic

/-!
-/

public meta section

open Lean Lean.Meta Lean.Elab.Tactic
open MeasureTheory

namespace RDo.Tactic

/-- Which `rdo` construct a program is made of, as far as the tactic is concerned. -/
inductive Shape
  /-- `return e`, elaborated to `MeasurableSpacePure.mPure e`. -/
  | mPure
  /-- `let x ← p; q`, elaborated to `MeasurableSpaceBind.mBind p q`. -/
  | mBind
  /-- `fun c ↦ κ (g c)`: a family `κ` that does not mention the parameter, read through a
  reparametrisation `g`. -/
  | comp
  /-- `fun c ↦ if p c then κ c else η c`: a if-then-else over two families of measures. -/
  | ite
  /-- `fun c ↦ if h : p c then κ c h else η c h`: a dependent if-then-else. The condition and the
  two branches are carried along, abstracted over the parameter, because `apply` cannot recover
  them: the branches take the proof, whereas the lemma indexes them by a subtype. -/
  | dite (p tb fb : Expr)
  /-- Anything else: a fixed distribution, a program the tactic was not taught about. These are
  the leaves of the recursion. -/
  | leaf
  --deriving Inhabited

/-- Recognise the construct a family of measures `κ : γ → Measure α` is built from. -/
def shapeOf (κ : Expr) : MetaM Shape := do
  let κ ← etaExpand (← whnfR κ)
  lambdaBoundedTelescope κ 1 fun cs body ↦ do
    let c := cs[0]!
    /- `etaExpand` rebuilds `κ` as `fun c ↦ (…) c`, so `body` is a beta-redex even when the
    original program was not an application. Normalising it once here is what makes the tests
    below look at the program itself rather than at that redex. -/
    let body ← whnfR body
    let head := body.getAppFn
    if head.isConstOf ``MeasurableSpacePure.mPure then
      return .mPure
    else if head.isConstOf ``MeasurableSpaceBind.mBind then
      return .mBind
    else if head.isConstOf ``ite then
      return .ite
    else if head.isConstOf ``dite then
      /- `dite` takes five arguments: the type, the condition, the `Decidable` instance, and the
      two branches. Only the last four matter, abstracted over `c`. -/
      let args := body.getAppArgs
      return .dite (← mkLambdaFVars #[c] args[1]!) (← mkLambdaFVars #[c] args[3]!)
        (← mkLambdaFVars #[c] args[4]!)
    else if body.isApp
      && !body.appFn!.containsFVar c.fvarId!
      && body.appArg!.containsFVar c.fvarId!
      && body.appArg! != c then
      /- The last conjunct rules out `body = κ c`, which is what `etaExpand` produces out of a
      program that was not a lambda to begin with. Without it, `IsMarkov ⇑κ` would be read as a
      reparametrisation of itself by the identity, and the recursion below would never end. -/
      return .comp
    else
      return .leaf

/-- Try to close a leaf goal `IsMarkov κ`, either by instance synthesis or from a hypothesis of the
local context. On failure the goal is handed back unchanged. -/
def closeLeaf (g : MVarId) : MetaM (List MVarId) := do
  if let .some proof ← trySynthInstance (← g.getType) then
    g.assign proof
    return []
  if ← g.assumptionCore then
    return []
  return [g]

/-- The constant heading the body of `κ`, when it is a definition the tactic could look through. -/
def programHeadDef? (κ : Expr) : MetaM (Option Name) := do
  let κ ← etaExpand (← whnfR κ)
  lambdaBoundedTelescope κ 1 fun _ body ↦ do
    let .const n _ := (← whnfR body).getAppFn | return none
    let some info := (← getEnv).find? n | return none
    return if info.hasValue then some n else none

/-- Default number of definitions `is_markov` looks through before giving up. -/
def defaultUnfoldFuel : Nat := 8

/-- Look through the definitions heading the program, until one of the constructs the tactic
knows shows up. This is what makes `unfold` unnecessary before `is_markov`. -/
partial def unfoldToKnownShape (target : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  unless target.isAppOfArity ``IsMarkov 5 do return none
  let some n ← programHeadDef? target.appArg! | return none
  let target' ← deltaExpand target (· == n)
  if target' == target then return none
  match ← shapeOf target'.appArg! with
  | .leaf => unfoldToKnownShape target' (fuel - 1)
  | _ => return some target'

/-- Turn a goal `IsMarkov κ` into the list of goals the user is left with. -/
partial def isMarkovCore (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := do
  let target ← instantiateMVars (← g.getType)
  -- `IsMarkov` takes five arguments: `γ`, `α`, their `MeasurableSpace` instances, and `κ`.
  unless target.isAppOfArity ``IsMarkov 5 do
    return [g]
  match ← shapeOf target.appArg! with
  | .mPure =>
    -- `return e`: one lemma, and the measurability of `e` is left to the user.
    g.applyConst ``IsMarkov.mPure_comp
  | .mBind =>
    -- `let x ← p; q`: two hypotheses, both `IsMarkov` goals, so we recurse into both.
    let mut goals := []
    for g' in ← g.applyConst ``IsMarkov.mBind do
      goals := goals ++ (← isMarkovCore g' fuel)
    return goals
  | .comp =>
    /- `fun c ↦ κ (g c)`: two hypotheses, one `IsMarkov` goal and one measurability goal, so we
    recurse into the first and leave the second to the user. -/
    let gs ← g.applyConst ``IsMarkov.comp
    match gs with
    | [g_is_markov, g_measurable] =>
      return (← isMarkovCore g_is_markov fuel) ++ [g_measurable]
    | _ =>
      throwError "is_markov: expected two goals after the `comp` step, got {gs.length}"
  | .ite =>
    /- `if p c then κ c else η c`: three hypotheses, one measurability goal and two `IsMarkov`
    goals, so we leave the first to the user and recurse into the last two -/
    let gs ← g.applyConst ``IsMarkov.ite
    match gs with
    | hd :: tl =>
      let mut goals := [hd]
      for g' in tl do
        goals := goals ++ (← isMarkovCore g' fuel)
      return goals
    | _ =>
      throwError "is_markov: expected at least one goal after the `ite` step, got {gs.length}"
  | .dite p tb fb =>
    /- `if h : p c then tb c h else fb c h`. The lemma indexes its branches by the subtypes
    `{c // p c}` and `{c // ¬ p c}`, so we reassociate the two branches into that form here
    (`κ x = tb x.1 x.2`) and build the application ourselves. -/
    let dom := (← inferType p).bindingDomain!
    let notP ← withLocalDeclD `c dom fun c => do
      mkLambdaFVars #[c] (← mkAppM ``Not #[(p.beta #[c])])
    let bundle (branch pred : Expr) : MetaM Expr := do
      let subtype ← mkAppM ``Subtype #[pred]
      withLocalDeclD `x subtype fun x => do
        let v ← mkAppM ``Subtype.val #[x]
        let h ← mkAppM ``Subtype.property #[x]
        mkLambdaFVars #[x] (mkApp2 branch v h).headBeta
    let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Measurable #[p])
    let hκ ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``IsMarkov #[← bundle tb p])
    let hη ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``IsMarkov #[← bundle fb notP])
    logInfo m!"hp: {← inferType hp} hκ : {← inferType hκ} hη : {← inferType hη}"
    let proof ← mkAppM ``IsMarkov.dite #[hp, hκ, hη]
    unless ← isDefEq (← g.getType) (← inferType proof) do
      throwError "is_markov: the `dite` step does not match the goal {indentExpr (← g.getType)}"
    g.assign proof
    return (← isMarkovCore hκ.mvarId! fuel) ++ (← isMarkovCore hη.mvarId! fuel) ++ [hp.mvarId!]
  | .leaf =>
    /- A leaf: either something already known — a fixed distribution, a hypothesis, a program
    with its own `IsMarkov` instance — or a definition still to be looked through. Closing comes
    first, so that a sub-program which has already been proved Markov is used as such rather than
    unfolded. -/
    let leftover ← closeLeaf g
    if leftover.isEmpty then return []
    /- The goal was not closed, so we try to unfold names in the head of the program until we reach
    a known shape. If that fails, we leave the goal to the user. -/
    match ← unfoldToKnownShape (← instantiateMVars (← g.getType)) fuel with
    | some target => isMarkovCore (← g.change target (checkDefEq := false)) fuel
    | none => return leftover

/-- A program with no parameter denotes a probability measure as soon as the constant family it
defines is a Markov kernel. -/
lemma isProbabilityMeasure_of_isMarkov {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : IsMarkov fun _ : Unit ↦ μ) : IsProbabilityMeasure μ :=
  h.isProbabilityMeasure ()

/-- Bring a goal of the form `IsProbabilityMeasure μ` into the form `IsMarkov fun _ : Unit ↦ μ`, so
that `isMarkovCore` can be applied. -/
def toIsMarkovGoal (g : MVarId) : MetaM MVarId := do
  let target ← instantiateMVars (← g.getType)
  unless target.isAppOfArity ``IsProbabilityMeasure 3 do
    return g
  match ← g.applyConst ``isProbabilityMeasure_of_isMarkov with
  | [g'] => return g'
  | gs =>
    throwError "is_markov: expected one goal after the `IsProbabilityMeasure` step, \
      got {gs.length}"

/-- Run `fun_prop` on a goal, and keep the goal unchanged if it fails. -/
def tryFunProp (g : MVarId) : TacticM (List MVarId) := do
  let tac ← `(tactic| try fun_prop)
  Lean.Elab.Tactic.run g (evalTactic tac)

/-- `is_markov` proves that an `rdo` program in the `MeasurableSpaceMonad` is a Markov kernel
(goal `RDo.IsMarkov prog`) or, for a program with no parameter, a probability measure
(goal `IsProbabilityMeasure prog`).

It walks through the structure of the program, and finishes by running `fun_prop` on each side
condition it produced. It automatically looks through definitions, so `unfold` is not needed before
`is_markov`. The number of definitions it looks through is limited to `8` by default but can be
changed by passing a `fuel` argument:

* `is_markov (fuel := n)` looks through up to `n` definitions.

Example:

```
noncomputable def prog : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y

example : IsProbabilityMeasure prog := by
  is_markov
```

It automatically looks through definitions, so `unfold` is not needed before `is_markov`. The
number of definitions it looks through is limited defaults to `8` but can be changed by passing a
`fuel` argument:

* `is_markov (fuel := 12)` looks through up to `12` definitions. -/
syntax (name := isMarkovTac) "is_markov" (" (" &"fuel" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| is_markov $[(fuel := $fuel?)]?) => classical do
    let fuel := (fuel?.map (·.getNat)).getD defaultUnfoldFuel
    let goals ← isMarkovCore (← toIsMarkovGoal (← getMainGoal)) fuel
    let mut remaining := []
    for g in goals do
      remaining := remaining ++ (← tryFunProp g)
    replaceMainGoal remaining

end RDo.Tactic

end
