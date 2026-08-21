/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.RDo.Tactic.Lemmas
public meta import Lean.Elab.Tactic.Basic

/-!
# The `is_markov` tactic

The tactic reads the program and decides itself which lemma to apply, rather than trying them all.
It works on goals of the form `RDo.IsMarkov κ`, where `κ : γ → Measure α` describes a program with
everything it has in scope gathered in the parameter `γ`.

The loop is three steps, repeated:

1. **look** at the body of `κ` under its binder, and recognise which `rdo` construct it is
   (`RDo.Tactic.shapeOf`);
2. **apply** the corresponding lemma of `LeanMachineLearning.RDo.Tactic.Lemmas`, which replaces
   the goal by its hypotheses;
3. **recurse** on the hypotheses that are again `IsMarkov` goals, and hand back the others.

What is handed back is exactly the measurability side conditions, plus any leaf the tactic did not
recognise. Nothing is attempted on them: proving them is the user's job, which is also what makes
the tactic predictable — it either consumes the whole structure of the program, or stops on a goal
that says precisely what is missing.

## Extending it

Adding a construct is two edits: a constructor in `RDo.Tactic.Shape` with the head constant it
matches on in `RDo.Tactic.shapeOf`, and the corresponding branch in `RDo.Tactic.isMarkovCore`
naming the lemma to apply. Nothing else in this file needs to change.
-/

public meta section

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic
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
  deriving Inhabited

/-- Recognise the construct a family of measures `κ : γ → Measure α` is built from.

`κ` is eta-expanded first, so that a program written point-free is looked at under a binder just
like any other, and its body is put in weak head normal form, which in particular unfolds the
`have`s the `rdo` elaborator leaves behind. Only the head constant of the body is examined. -/
def shapeOf (κ : Expr) : MetaM Shape := do
  let κ ← etaExpand (← whnfR κ)
  lambdaBoundedTelescope κ 1 fun cs body ↦ do
    let c := cs[0]!
    -- `etaExpand` rebuilds `κ` as `fun c ↦ (…) c`, so `body` is a beta-redex even when the
    -- original program was not an application. Normalising it once here is what makes the tests
    -- below look at the program itself rather than at that redex.
    let body ← whnfR body
    let head := body.getAppFn
    if head.isConstOf ``MeasurableSpacePure.mPure then
      return .mPure
    else if head.isConstOf ``MeasurableSpaceBind.mBind then
      return .mBind
    else if head.isConstOf ``ite then
      return .ite
    else if head.isConstOf ``dite then
      -- `dite` takes five arguments: the type, the condition, the `Decidable` instance, and the
      -- two branches. Only the last four matter, abstracted over `c`.
      let args := body.getAppArgs
      return .dite (← mkLambdaFVars #[c] args[1]!) (← mkLambdaFVars #[c] args[3]!)
        (← mkLambdaFVars #[c] args[4]!)
    else if body.isApp
      && !body.appFn!.containsFVar c.fvarId!
      && body.appArg!.containsFVar c.fvarId!
      && body.appArg! != c then
      /- The last conjunct rules out `body = κ c`, which is what `etaExpand` produces out of a
      program that was not a lambda to begin with. Without it, `IsMarkov ⇑κ` would be read as a
      reparametrisation of itself by the identity, and the recursion below would never end.

      `κ` does not mention `c`, so it is already a closed term and escapes the telescope as it
      is; `g` is the argument abstracted over `c`, which has to be built here, while `c` is
      still in scope. -/
      return .comp
    else
      return .leaf

/-- Try to close a leaf goal `IsMarkov κ`, either by instance synthesis — this is how
`RDo.IsMarkov.const` discharges a fixed distribution — or from a hypothesis of the local context.
On failure the goal is handed back unchanged. -/
def closeLeaf (g : MVarId) : MetaM (List MVarId) := do
  if let .some proof ← trySynthInstance (← g.getType) then
    g.assign proof
    return []
  if ← g.assumptionCore then
    return []
  return [g]

/-- The constant heading the body of `κ`, when it is a definition the tactic could look through.

This is only ever asked of a program the recursion did not recognise, so the constructs of
`RDo.Tactic.Shape` cannot come out of it and need no protecting. -/
def programHeadDef? (κ : Expr) : MetaM (Option Name) := do
  let κ ← etaExpand (← whnfR κ)
  lambdaBoundedTelescope κ 1 fun _ body ↦ do
    let .const n _ := (← whnfR body).getAppFn | return none
    let some info := (← getEnv).find? n | return none
    return if info.hasValue then some n else none

/-- How many definitions `is_markov` looks through before giving up. Raise it on a call with
`is_markov (fuel := 20)`. -/
def defaultUnfoldFuel : Nat := 8

/-- Look through the definitions heading the program, until one of the constructs the tactic
knows shows up. This is what makes `unfold` unnecessary before `is_markov`.

The search runs on the *target*, not on the goal, and returns the new target rather than a new
goal. Changing the goal at each step would assign it, and a search that ends in failure would
then leave the original goal assigned to an unreachable one — the proof term would keep a hole.
The caller changes the goal once, if the search succeeded.

`none` is returned when no known construct is ever reached, and the caller then keeps the goal as
it was: the user is shown the program they wrote, not a delta-expanded version of it. Requiring a
known shape is also what bounds the search — every successful unfolding is immediately consumed by
the recursion.

Note that the target has to be instantiated before being passed in: right after an `apply` it is
still `IsMarkov ?κ`, and there would be nothing to unfold in it. -/
partial def unfoldToKnownShape (target : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  unless target.isAppOfArity ``RDo.IsMarkov 5 do return none
  let some n ← programHeadDef? target.appArg! | return none
  let target' ← deltaExpand target (· == n)
  if target' == target then return none
  match ← shapeOf target'.appArg! with
  | .leaf => unfoldToKnownShape target' (fuel - 1)
  | _ => return some target'

/-- Turn a goal `IsMarkov κ` into the list of goals the user is left with.

The recursion is on the structure of the program: each `mBind` produces two `IsMarkov` goals, on
which the function calls itself, and each `mPure` produces a measurability goal, on which it does
not. A goal that is not an `IsMarkov` goal at all is returned untouched. -/
partial def isMarkovCore (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := do
  let target ← instantiateMVars (← g.getType)
  -- `IsMarkov` takes five arguments: `γ`, `α`, their `MeasurableSpace` instances, and `κ`.
  unless target.isAppOfArity ``RDo.IsMarkov 5 do
    return [g]
  match ← shapeOf target.appArg! with
  | .mPure =>
    -- `return e`: one lemma, and the measurability of `e` is left to the user.
    g.applyConst ``RDo.IsMarkov.mPure_comp
  | .mBind =>
    -- `let x ← p; q`: two hypotheses, both `IsMarkov` goals, so we recurse into both.
    let mut goals := []
    for g' in ← g.applyConst ``RDo.IsMarkov.mBind do
      goals := goals ++ (← isMarkovCore g' fuel)
    logInfo m!"goals after mBind: {goals}"
    return goals
  | .comp =>
    let gs ← g.applyConst ``RDo.IsMarkov.comp
    match gs with
    | [g_is_markov, g_measurable] =>
      return (← isMarkovCore g_is_markov fuel) ++ [g_measurable]
    | _ =>
      throwError "is_markov: expected two goals after the `comp` step, got {gs.length}"
  | .ite =>
    let gs ← g.applyConst ``RDo.IsMarkov.ite
    logInfo m!"goals after ite: {gs}"
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
    `{c // p c}` and `{c // ¬ p c}`, so we reassociate the two branches into that form here —
    `κ x = tb x.1 x.2` — and build the application ourselves. -/
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
    let hκ ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``RDo.IsMarkov #[← bundle tb p])
    let hη ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``RDo.IsMarkov #[← bundle fb notP])
    let proof ← mkAppM ``RDo.IsMarkov.diteP #[hp, hκ, hη]
    unless ← isDefEq (← g.getType) (← inferType proof) do
      throwError "is_markov: the `dite` step does not match the goal{indentExpr (← g.getType)}"
    g.assign proof
    return (← isMarkovCore hκ.mvarId! fuel) ++ (← isMarkovCore hη.mvarId! fuel) ++ [hp.mvarId!]
  | .leaf =>
    /- A leaf: either something already known — a fixed distribution, a hypothesis, a program
    with its own `IsMarkov` instance — or a definition still to be looked through. Closing comes
    first, so that a sub-program which has already been proved Markov is used as such rather than
    unfolded. -/
    let leftover ← closeLeaf g
    if leftover.isEmpty then return []
    match ← unfoldToKnownShape (← instantiateMVars (← g.getType)) fuel with
    | some target => isMarkovCore (← g.change target (checkDefEq := false)) fuel
    | none => return leftover

/-- Bring the goal to the form the recursion expects.

A goal `IsProbabilityMeasure t` is about a program with no parameter;
`RDo.isProbabilityMeasure_of_isMarkov` restates it as `IsMarkov fun _ : Unit ↦ t`. Any other
goal is passed on unchanged, and `RDo.Tactic.isMarkovCore` will hand it back if it is not an
`IsMarkov` goal. -/
def toIsMarkovGoal (g : MVarId) : MetaM MVarId := do
  let target ← instantiateMVars (← g.getType)
  unless target.isAppOfArity ``MeasureTheory.IsProbabilityMeasure 3 do
    return g
  match ← g.applyConst ``RDo.isProbabilityMeasure_of_isMarkov with
  | [g'] => return g'
  | gs =>
    throwError "is_markov: expected one goal after the `IsProbabilityMeasure` step, \
      got {gs.length}"

/-- Run `fun_prop` on a goal, and keep the goal unchanged if it fails.

`try` is what makes this total: no exception escapes, so there is no state to roll back, and a
goal `fun_prop` cannot prove simply comes back out. Applied to an `IsMarkov` goal — a leaf the
recursion could not decompose — it fails and the goal is preserved, which is what we want. -/
def tryFunProp (g : MVarId) : TacticM (List MVarId) := do
  let tac ← `(tactic| try fun_prop)
  Lean.Elab.Tactic.run g (evalTactic tac)

/--
`is_markov` proves that an `rdo` program in the `MeasureTheory.Measure` monad is a Markov kernel
(goal `RDo.IsMarkov κ`) or, for a program with no parameter, a probability measure
(goal `IsProbabilityMeasure t`).

It walks through the structure of the program, and finishes by running `fun_prop` on each side
condition it produced. On a program built from measurable pieces nothing is left:

```
noncomputable def prog : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y

example : IsProbabilityMeasure prog := by
  is_markov
```

What `fun_prop` cannot prove is handed back untouched, so the goals one is left with are exactly
the ones that need a human. Dropping the `tryFunProp` loop in the tactic below restores the raw
output of `RDo.Tactic.isMarkovCore`, which is what to look at when the tactic misbehaves.

The program does not have to be unfolded by hand: a goal about a definition is looked through
until one of the constructs below appears. At most `RDo.Tactic.defaultUnfoldFuel` definitions are
looked through in a row; when a program is layered more deeply than that, the goal comes back
undisturbed and `is_markov (fuel := 20)` raises the bound.

`return`, `let x ← _`, and a known Markov family read through a function of the parameter are
understood. On anything else the tactic stops and hands back the `IsMarkov` goal it could not
decompose.
-/
syntax (name := isMarkovTac) "is_markov" (" (" &"fuel" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| is_markov $[(fuel := $fuel?)]?) => do
    let fuel := (fuel?.map (·.getNat)).getD defaultUnfoldFuel
    let goals ← isMarkovCore (← toIsMarkovGoal (← getMainGoal)) fuel
    let mut remaining := []
    for g in goals do
      remaining := remaining ++ (← tryFunProp g)
    replaceMainGoal remaining

end RDo.Tactic
