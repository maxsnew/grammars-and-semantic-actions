import LambekD.Elab.Base
import LambekD.Core.Connectives

/-!
# Elaborator utility functions

String manipulation, variable location, grammar abstraction, and
type matching helpers for the ordered linear DSL elaborator.
-/

namespace LambekD.Elab

open Lean Elab Term Meta
open LambekD

partial def collectAllIdents (stx : Syntax) : Lean.NameSet :=
  go stx {}
where
  go (stx : Syntax) (acc : Lean.NameSet) : Lean.NameSet :=
    match stx with
    | .missing => acc
    | .atom .. => acc
    | .ident _ _ val _ => acc.insert val
    | .node _ _ args => args.foldl (fun a arg => go arg a) acc

def concatStrs (cfg : ElabConfig) (ctx : OrderedCtx) (start stop : Nat) : TermElabM Expr := do
  if start >= stop then
    mkAppOptM ``List.nil #[some cfg.alphabetTy]
  else if start + 1 == stop then
    return (ctx.getV start).strExpr
  else
    -- Fold right: w₁ ++ (w₂ ++ (w₃ ++ ...))
    -- This matches how splitting builds strings: splitting wL wR gives wL ++ wR,
    -- and the right part is itself a right-folded concatenation.
    let mut result := (ctx.getV (stop - 1)).strExpr
    for i in List.range (stop - start - 1) do
      let idx := stop - 2 - i
      result ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, result]
    return result

def findSplit (leftStx rightStx : Syntax) (ctx : OrderedCtx) (start stop : Nat)
    (aliases : AliasMap := {}) (recCallName : Option Name := none)
    : TermElabM Nat := do
  let leftNames  := resolveAliases aliases (collectAllIdents leftStx)
  let rightNames := resolveAliases aliases (collectAllIdents rightStx)
  -- When the right expression contains a recursive call, trailing unused variables
  -- are consumed by the induction hypothesis (through the motive).
  let allowTrailing := match recCallName with
    | some rn => (collectAllIdents rightStx).contains rn
    | none => false
  let mut leftMax : Option Nat := none
  let mut rightMin : Option Nat := none
  for i in [start : stop] do
    let name := (ctx.getV i).userName
    let inLeft := leftNames.contains name
    let inRight := rightNames.contains name
    if inLeft && inRight then
      throwError "linear variable '{name}' used in both sides of multiplicative operation (contraction)"
    if inLeft then
      leftMax := some i
    if inRight then
      if rightMin.isNone then rightMin := some i
    if !inLeft && !inRight then
      if !allowTrailing then
        throwError "linear variable '{name}' unused in multiplicative operation (weakening)"
  match leftMax, rightMin with
  | none, none   => return start
  | some _, none  => return stop
  | none, some _  => return start
  | some lm, some rm =>
    if lm >= rm then
      throwError "ordering violation: left-side variables appear after right-side variables"
    return lm + 1

def locateVars (stx : Syntax) (ctx : OrderedCtx) (start stop : Nat)
    (aliases : AliasMap := {})
    : TermElabM (Nat × Nat) := do
  let names := resolveAliases aliases (collectAllIdents stx)
  let mut lo := start
  let mut hi := start
  let mut foundAny := false
  for i in [start : stop] do
    if names.contains (ctx.getV i).userName then
      if !foundAny then
        lo := i
        foundAny := true
      hi := i + 1
  if !foundAny then
    return (start, start)
  for i in [lo : hi] do
    if !names.contains (ctx.getV i).userName then
      throwError "ordering violation: variable '{(ctx.getV i).userName}' between variables used by sub-expression"
  return (lo, hi)

def replaceSlice (ctx : OrderedCtx) (start stop tStart tStop : Nat)
    (newVars : Array OrderedVar) : OrderedCtx × Nat × Nat :=
  let before := ctx[start:tStart]
  let after := ctx[tStop:stop]
  let prefix_ := ctx[0:start]
  let suffix_ := ctx[stop:ctx.size]
  let newCtx := prefix_.toArray ++ before.toArray ++ newVars ++ after.toArray ++ suffix_.toArray
  let newStart := start
  let newStop := start + (tStart - start) + newVars.size + (stop - tStop)
  (newCtx, newStart, newStop)

/-- Abstract a type over a string variable to form a Grammar, with eta-reduction.
    If `ty = F wVar` where `F` doesn't reference `wVar`, returns `F` directly
    instead of `fun wVar => F wVar`. -/
def abstractGrammar (wVar : Expr) (ty : Expr) : TermElabM Expr := do
  -- Check if ty is `F wVar` where F doesn't contain wVar
  if ty.isApp then
    let fn := ty.appFn!
    let arg := ty.appArg!
    if arg == wVar && !fn.containsFVar wVar.fvarId! then
      return fn
  mkLambdaFVars #[wVar] ty

/-- Like `abstractGrammar` but first does `Expr.replace` to swap `oldVar` for `wVar`. -/
def abstractGrammarReplace (wVar : Expr) (ty : Expr) (oldVar : Expr) : TermElabM Expr :=
  abstractGrammar wVar (ty.replace fun e => if e == oldVar then some wVar else none)

def mkGrammarTy (cfg : ElabConfig) : MetaM Expr :=
  mkArrow cfg.stringTy (mkSort (.succ cfg.gramLevel))

/-- Prove `a = b` for string expressions. Returns `Eq.refl a` if definitionally equal,
    otherwise uses `simp [List.append_assoc]`. -/
def proveStrEq (a b : Expr) : TermElabM Expr := do
  if ← isDefEq a b then
    mkEqRefl a
  else
    let eqType ← mkEq a b
    elabTerm (← `(by simp [List.append_assoc])) (some eqType)

/-- Try to match `goal` as a grammar constructor applied to args.
    First tries direct match on whnf; if that's a lambda `fun w => F w`,
    eta-reduces to `F` (without whnf'ing the body, to preserve the head). -/
def etaReduceGrammar (goal : Expr) : MetaM Expr := do
  -- Use withReducible so whnf doesn't unfold LinFunR, Tensor, etc.
  -- (they are `def`, not `abbrev`). This preserves the grammar constructor heads.
  let g ← withReducible <| whnf goal
  match g with
  | .lam _ _ body _ =>
    -- fun w => F w  →  check if body = F (bvar 0), then return F
    -- Don't whnf body — we want to preserve `Sum A B` etc.
    if body.isApp then
      let fn := body.appFn!
      let arg := body.appArg!
      if arg == .bvar 0 && !fn.hasLooseBVars then
        return fn
    return g
  | _ => return g

end LambekD.Elab
