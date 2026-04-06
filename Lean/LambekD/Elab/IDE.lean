import LambekD.Elab.Util

/-!
# IDE integration for the ordered linear DSL

Linear context formatting and info-tree registration for
IDE hover/infoview display.
-/

namespace LambekD.Elab

open Lean Elab Term Meta
open LambekD

/-- Format the linear context for IDE display.
    Shows linear variables with eta-reduced grammar types.
    Synthetic variables (backing product patterns) are hidden;
    their user-facing aliases are shown instead. -/
def formatLinearCtx (ctx : OrderedCtx) (start stop : Nat)
    (aliases : AliasMap) (goal : Expr) : TermElabM MessageData := do
  -- Collect names that are alias targets (synthetic product vars)
  let mut syntheticNames : Lean.NameSet := {}
  for (_, alias) in aliases.toList do
    syntheticNames := syntheticNames.insert alias.ctxName
  let mut parts : Array MessageData := #[]
  for i in [start : stop] do
    let v := ctx.getV i
    -- Skip synthetic product variables (they're shown via aliases)
    if !syntheticNames.contains v.userName then
      let g ← etaReduceGrammar v.grammar
      parts := parts.push m!"{v.userName} : {g}"
  for (name, alias) in aliases.toList do
    let g ← etaReduceGrammar alias.projGrammar
    parts := parts.push m!"{name} : {g}"
  let goalReduced ← etaReduceGrammar goal
  let ctxLines := MessageData.joinSep parts.toList (.ofFormat "\n")
  if parts.isEmpty then
    return m!"⊢ {goalReduced}"
  else
    return m!"Linear:\n{ctxLines}\n⊢ {goalReduced}"

/-- Collect all free variable IDs occurring in an expression. -/
private partial def collectFVarIds : Expr → FVarIdHashSet → FVarIdHashSet
  | .fvar id, acc => acc.insert id
  | .app f a, acc => collectFVarIds a (collectFVarIds f acc)
  | .lam _ t b _, acc => collectFVarIds b (collectFVarIds t acc)
  | .forallE _ t b _, acc => collectFVarIds b (collectFVarIds t acc)
  | .letE _ t v b _, acc => collectFVarIds b (collectFVarIds v (collectFVarIds t acc))
  | .mdata _ e, acc => collectFVarIds e acc
  | .proj _ _ e, acc => collectFVarIds e acc
  | _, acc => acc

/-- Register the linear context in the info tree so the IDE infoview
    shows linear variables when the cursor is on a gterm node. -/
def registerLinearCtxInfo (stx : Syntax) (ctx : OrderedCtx) (start stop : Nat)
    (aliases : AliasMap) (goal : Expr) : TermElabM Unit := do
  -- Identify synthetic product-pattern variables
  let mut syntheticNames : Lean.NameSet := {}
  for (_, alias) in aliases.toList do
    syntheticNames := syntheticNames.insert alias.ctxName
  -- Collect fvar IDs referenced in grammar/goal expressions so their
  -- declarations (A, B, C, …) can be included for name resolution.
  let mut refFVars : FVarIdHashSet := {}
  for i in [start : stop] do
    let v := ctx.getV i
    if !syntheticNames.contains v.userName then
      let g ← etaReduceGrammar v.grammar
      refFVars := collectFVarIds g refFVars
  for (_, alias) in aliases.toList do
    let g ← etaReduceGrammar alias.projGrammar
    refFVars := collectFVarIds g refFVars
  let goalReduced ← etaReduceGrammar goal
  refFVars := collectFVarIds goalReduced refFVars
  -- Build custom lctx: referenced non-linear vars + linear vars
  let currentLctx ← getLCtx
  let mut lctx : LocalContext := {}
  lctx ← currentLctx.foldlM (init := lctx) fun acc decl =>
    if refFVars.contains decl.fvarId then
      return acc.mkLocalDecl decl.fvarId decl.userName decl.type decl.binderInfo
    else
      return acc
  -- Add linear variables (annotated so they're distinguishable)
  for i in [start : stop] do
    let v := ctx.getV i
    if !syntheticNames.contains v.userName then
      let g ← etaReduceGrammar v.grammar
      let fvarId ← mkFreshFVarId
      let linName := Name.mkSimple s!"{v.userName} [linear]"
      lctx := lctx.mkLocalDecl fvarId linName g
  -- Add aliases (product pattern projections, also linear)
  for (name, alias) in aliases.toList do
    let g ← etaReduceGrammar alias.projGrammar
    let fvarId ← mkFreshFVarId
    let linName := Name.mkSimple s!"{name} [linear]"
    lctx := lctx.mkLocalDecl fvarId linName g
  -- Register as term info with the goal as expected type
  let mvar ← mkFreshExprMVar (some goalReduced)
  addTermInfo' stx mvar (expectedType? := some goalReduced) (lctx? := some lctx)

end LambekD.Elab
