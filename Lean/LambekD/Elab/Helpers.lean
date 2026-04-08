import LambekD.Elab.Syntax
import LambekD.Elab.Match
import LambekD.Elab.Inductive

/-!
# Elaborator helper functions

CPS binder introduction, NL pattern resolution, splitting proofs,
and other utilities used by the ordered linear term elaborator.
-/

namespace LambekD.Elab

open Lean Elab Term Meta
open LambekD

/-- Type alias for the recursive elaboration callback.
    Used by extracted elaboration cases (Application, CaseRec) to call
    back into `elaborateOrderedTerm` without circular imports. -/
abbrev ElabFn := ElabConfig → TSyntax `gterm → OrderedCtx → Nat → Nat → Expr → AliasMap → TermElabM Expr

/-- CPS-introduce IH binders for recursive components of a `.rec` branch.
    `ihInfos` is an array of `(userName, ihType)` pairs. Calls `k` with the
    accumulated IH fvars and a map from user variable names to IH expressions. -/
partial def withRecIHBinders (ihInfos : Array (Name × Expr)) (idx : Nat)
    (accFvars : Array Expr) (accMap : Std.HashMap Name Expr)
    (k : Array Expr → Std.HashMap Name Expr → TermElabM Expr)
    : TermElabM Expr := do
  if h : idx < ihInfos.size then
    let (nm, ty) := ihInfos[idx]
    let ihDeclName := Name.mkSimple s!"_ih_{nm}"
    withLocalDecl ihDeclName .default ty fun ihVar =>
      withRecIHBinders ihInfos (idx + 1) (accFvars.push ihVar) (accMap.insert nm ihVar) k
  else
    k accFvars accMap

/-- Build proof that the concatenation of component strings equals `wBr`,
    given the splitting fvars from `withTensorCtorComponents`.
    `splittings[0] : Splitting wBr`, `splittings[i+1] : Splitting splittings[i].right`.
    Returns: `componentConcat = wBr`. -/
partial def proveSplittingsEq (cfg : ElabConfig) (splittings : Array Expr) (idx : Nat)
    : TermElabM Expr := do
  let s := splittings[idx]!
  if idx == splittings.size - 1 then
    mkAppM ``Splitting.eq #[s]
  else
    let innerProof ← proveSplittingsEq cfg splittings (idx + 1)
    let sLeft ← mkAppM ``Splitting.left #[s]
    let appendFn ← withLocalDecl `_x .default cfg.stringTy fun x => do
      let body ← mkAppM ``HAppend.hAppend #[sLeft, x]
      mkLambdaFVars #[x] body
    let congrProof ← mkAppM ``congrArg #[appendFn, innerProof]
    let sEq ← mkAppM ``Splitting.eq #[s]
    mkAppM ``Eq.trans #[congrProof, sEq]

/-- CPS helper: introduce non-linear binders from a constructor type using
    names from the user's pattern. Walks the ctor type, introducing `withLocalDecl`
    for each non-linear binder (stopping after exactly `nNonLin` binders or when
    we reach `w : String`). Calls `k` with `(nlFvars, tyStartingFromW)`. -/
partial def withNonLinearBranchBinders (cfg : ElabConfig) (cty : Expr)
    (nlNames : Array Name) (nNonLin : Nat) (idx : Nat) (acc : Array Expr)
    (k : Array Expr → Expr → TermElabM Expr) : TermElabM Expr := do
  if idx >= nNonLin then
    k acc cty
  else
    match cty with
    | .forallE _ dom body _ =>
      let domW ← whnf dom
      let isStr ← withReducible <| isDefEq domW cfg.stringTy
      if isStr then
        k acc cty  -- reached w : String, stop early
      else
        let name := if h : idx < nlNames.size then nlNames[idx] else Name.mkSimple s!"_nl_{idx}"
        withLocalDecl name .default dom fun nlVar => do
          withNonLinearBranchBinders cfg (body.instantiate1 nlVar) nlNames nNonLin (idx + 1) (acc.push nlVar) k
    | _ => k acc cty

/-- Info about a pattern match on a non-linear binder.
    Used to wrap the branch body in casesOn after elaboration. -/
structure NLPatternInfo where
  binderIdx : Nat           -- index in nlFvars array
  nlFvar : Expr             -- the lambda parameter fvar (of the original binder type)
  patVarFvars : Array Expr  -- pattern variable fvars
  ctorIdx : Nat             -- which constructor arm matches

/-- Parse pattern head: `some n` → (`some`, #[n]), `none` → (`none`, #[]),
    `0` → (`zero`, #[]). -/
def parseNLPatternHead (stx : Syntax) : TermElabM (Name × Array Syntax) := do
  if let some n := stx.isNatLit? then
    if n == 0 then return (`zero, #[])
    else throwError "numeric literal patterns > 0 not yet supported in NL patterns"
  if stx.getKind == ``Lean.Parser.Term.app then
    let head := stx[0]
    let argNode := stx[1]
    unless head.isIdent do
      throwError "pattern head must be an identifier, got {head}"
    let headName := head.getId
    let args := if argNode.getKind == `null then argNode.getArgs else #[argNode]
    return (headName, args)
  if stx.isIdent then
    return (stx.getId, #[])
  throwError "unsupported pattern syntax: {stx}"

/-- Resolve a pattern syntax against a type to get (ctorIdx, patVarNames, patVarTypes). -/
def resolveNLPattern (ty : Expr) (patStx : Syntax) : TermElabM (Nat × Array Name × Array Expr) := do
  let tyW ← whnf ty
  let indName := tyW.getAppFn.constName!
  let env ← getEnv
  let some indVal := getInductiveVal env indName
    | throwError "pattern match on non-inductive type {indName}"
  let (ctorShortName, argStxs) ← parseNLPatternHead patStx
  let mut foundCtor : Option (Nat × Name) := none
  for (cn, i) in indVal.ctors.zipIdx.toArray do
    let shortName := cn.replacePrefix indName .anonymous
    if shortName == ctorShortName then
      foundCtor := some (i, cn)
      break
  let some (idx, fullCtorName) := foundCtor
    | throwError "constructor '{ctorShortName}' not found in {indName}"
  let some ci := env.find? fullCtorName | throwError "ctor not found: {fullCtorName}"
  let indLevels := tyW.getAppFn.constLevels!
  let ctorTy := ci.type.instantiateLevelParams ci.levelParams indLevels
  let indArgs := tyW.getAppArgs
  let numParams := indVal.numParams
  let mut cty := ctorTy
  for p in indArgs[:numParams] do
    match cty with
    | .forallE _ _ b _ => cty := b.instantiate1 p
    | _ => throwError "unexpected ctor shape"
  let mut names : Array Name := #[]
  let mut types : Array Expr := #[]
  let mut argIdx := 0
  let mut curTy := cty
  for _ in [:100] do
    match curTy with
    | .forallE n d b _ =>
      if b.hasLooseBVars then
        let mv ← mkFreshExprMVar (some d)
        curTy := b.instantiate1 mv
      else
        curTy := b
      let argName := if h : argIdx < argStxs.size then
        if argStxs[argIdx].isIdent then argStxs[argIdx].getId
        else Name.mkSimple s!"_pat_{argIdx}"
      else n
      names := names.push argName
      types := types.push d
      argIdx := argIdx + 1
    | _ => break
  return (idx, names, types)

/-- CPS helper: like withNonLinearBranchBinders but supports patterns.
    For bare idents: introduces withLocalDecl as before.
    For patterns: introduces the binder AND pattern variables, instantiates
    ctor type with the constructor expression (not the raw binder).
    Calls `k` with `(nlFvars, patternInfos, tyStartingFromW)`. -/
partial def withNonLinearBranchBindersExt (cfg : ElabConfig) (cty : Expr)
    (nlInfos : Array NLBinderInfo) (nNonLin : Nat) (idx : Nat)
    (accFvars : Array Expr) (accPats : Array NLPatternInfo)
    (k : Array Expr → Array NLPatternInfo → Expr → TermElabM Expr) : TermElabM Expr := do
  if idx >= nNonLin then
    k accFvars accPats cty
  else
    match cty with
    | .forallE _ dom body _ =>
      let domW ← whnf dom
      let isStr ← withReducible <| isDefEq domW cfg.stringTy
      if isStr then
        k accFvars accPats cty  -- reached w : String, stop early
      else
        let info := if h : idx < nlInfos.size then nlInfos[idx] else .ident (Name.mkSimple s!"_nl_{idx}")
        match info with
        | .ident name =>
          withLocalDecl name .default dom fun nlVar => do
            withNonLinearBranchBindersExt cfg (body.instantiate1 nlVar) nlInfos nNonLin (idx + 1)
              (accFvars.push nlVar) accPats k
        | .pattern freshName patternStx =>
          -- Introduce the binder (lambda parameter)
          withLocalDecl freshName .default dom fun nlVar => do
            let patVarsAndCtor ← resolveNLPattern dom patternStx
            let (ctorIdx, patVarNames, patVarTypes) := patVarsAndCtor
            let rec introPatVars (names : Array Name) (types : Array Expr) (i : Nat)
                (acc : Array Expr) (k' : Array Expr → TermElabM Expr) : TermElabM Expr := do
              if h : i < names.size then
                withLocalDecl names[i] .default types[i]! fun fv =>
                  introPatVars names types (i + 1) (acc.push fv) k'
              else k' acc
            introPatVars patVarNames patVarTypes 0 #[] fun patVarFvars => do
              let ctorExpr ← buildCtorExpr dom ctorIdx patVarFvars
              let instBody := body.instantiate1 ctorExpr
              let patInfo : NLPatternInfo := ⟨accFvars.size, nlVar, patVarFvars, ctorIdx⟩
              withNonLinearBranchBindersExt cfg instBody nlInfos nNonLin (idx + 1)
                (accFvars.push nlVar) (accPats.push patInfo) k
    | _ => k accFvars accPats cty
where
  resolveNLPattern := LambekD.Elab.resolveNLPattern
  parsePatternHead := parseNLPatternHead
  /-- Build a constructor expression from pattern variable fvars.
      Uses the inductive type info from `ty` to find the right constructor. -/
  buildCtorExpr (ty : Expr) (ctorIdx : Nat) (patVarFvars : Array Expr) : TermElabM Expr := do
    let tyW ← whnf ty
    let indName := tyW.getAppFn.constName!
    let env ← getEnv
    let some indVal := getInductiveVal env indName
      | throwError "not an inductive: {indName}"
    let ctorName := indVal.ctors[ctorIdx]!
    let indLevels := tyW.getAppFn.constLevels!
    let indArgs := tyW.getAppArgs
    let numParams := indVal.numParams
    let some ci := env.find? ctorName | throwError "ctor not found: {ctorName}"
    let ctorLevels := ci.levelParams.map fun lp =>
      match indLevels.zip indVal.levelParams |>.find? (·.2 == lp) with
      | some (l, _) => l
      | none => .zero
    let mut result := Lean.mkConst ctorName ctorLevels
    for p in indArgs[:numParams] do
      result := mkApp result p
    for fv in patVarFvars do
      result := mkApp result fv
    return result

/-- Extract extra index expressions from a constructor's return type.
    `tyFromW` starts at `∀ (w : String), ...` with NL fvars already instantiated.
    Opens with `wExpr`, then opens remaining grammar foralls with metavars,
    reads the return type's index positions (between params and w). -/
def extractBranchIndexExprs (tyFromW : Expr) (wExpr : Expr)
    (numParams numExtraIndices : Nat) : MetaM (Array Expr) := do
  if numExtraIndices == 0 then return #[]
  match tyFromW with
  | .forallE _ _ afterW _ =>
    let body := afterW.instantiate1 wExpr
    let (_, _, retTy) ← forallMetaTelescope body
    let retArgs := retTy.getAppArgs
    return retArgs[numParams : numParams + numExtraIndices].toArray
  | _ => return #[]

/-- CPS-introduce equality binders for casesOn branches.
    `eqInfos` is an array of `(name, eqType)` pairs. -/
partial def withEqBinders (eqInfos : Array (Name × Expr)) (idx : Nat)
    (acc : Array Expr)
    (k : Array Expr → TermElabM Expr) : TermElabM Expr := do
  if h : idx < eqInfos.size then
    let (nm, ty) := eqInfos[idx]
    withLocalDecl nm .default ty fun fvar =>
      withEqBinders eqInfos (idx + 1) (acc.push fvar) k
  else
    k acc

/-- CPS-introduce motive index binders from the inductive type's foralls (after params).
    Stops after `remaining` binders (= numExtraIndices). -/
partial def withMotiveIdxBinders (tyRem : Expr) (remaining : Nat) (acc : Array Expr)
    (k : Array Expr → TermElabM Expr) : TermElabM Expr := do
  if remaining == 0 then k acc
  else
    match tyRem with
    | .forallE _ dom body _ =>
      let name := Name.mkSimple s!"_idx_{acc.size}"
      withLocalDecl name .default dom fun fvar =>
        withMotiveIdxBinders (body.instantiate1 fvar) (remaining - 1) (acc.push fvar) k
    | _ => throwError "unexpected inductive type shape for index binder"

/-- Check if a ctor type (after instantiating params) contains a genuine `w : String` binder.
    When Lean promotes `w` to a parameter, the ctor type no longer has a String forall,
    and all NL binders before `w` were also promoted. Returns `false` in that case. -/
def hasStringBinder (cfg : ElabConfig) (cty : Expr) : TermElabM Bool := do
  let mut ty := cty
  for _ in [:100] do
    match ty with
    | .forallE _ dom body _ =>
      if ← withReducible <| isDefEq (← whnf dom) cfg.stringTy then return true
      let mv ← mkFreshExprMVar (some dom)
      ty := body.instantiate1 mv
    | _ => return false
  return false

/-- CPS helper: introduce pattern variable local decls, then call k with the fvars. -/
partial def withPatternVarDecls {α : Type} (names : Array Name) (types : Array Expr) (idx : Nat) (acc : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α := do
  if h : idx < names.size then
    withLocalDecl names[idx] .default types[idx]! fun fv =>
      withPatternVarDecls names types (idx + 1) (acc.push fv) k
  else k acc

/-- Build the full string expression for a motive, replacing the scrutinee portion
    [tStart, tStop) with `wBr` and preserving context prefix/suffix. -/
def buildMotiveStr (cfg : ElabConfig) (ctx : OrderedCtx)
    (start _stop tStart tStop : Nat) (wBr : Expr) : TermElabM Expr := do
  let mut motiveStr := wBr
  if tStop < _stop then
    let afterStr ← concatStrs cfg ctx tStop _stop
    motiveStr ← mkAppM ``HAppend.hAppend #[motiveStr, afterStr]
  for i in List.range (tStart - start) do
    let idx := tStart - 1 - i
    motiveStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, motiveStr]
  return motiveStr

/-- Cast `branchExpr : goal(actualStr)` to `goal(motiveResultStr)` via splitting
    equality proofs from tensor decomposition. Shared by both rec and casesOn
    multi-arity tensor paths.
    Returns the cast expression, or `branchExpr` unchanged if no cast is needed. -/
def castViaSplittings (cfg : ElabConfig) (goal : Expr)
    (ctx : OrderedCtx) (start stop tStart tStop : Nat)
    (branchExpr : Expr) (newCtx : OrderedCtx) (newStart newStop : Nat)
    (comps : Array (Expr × Expr × Expr)) (fvars : Array Expr) (wBr : Expr)
    : TermElabM Expr := do
  let actualStr ← concatStrs cfg newCtx newStart newStop
  let motiveResultStr ← buildMotiveStr cfg ctx start stop tStart tStop wBr
  if ← isDefEq actualStr motiveResultStr then
    pure branchExpr
  else
    let splittings := (List.range (comps.size - 1)).toArray.map fun i => fvars[2 * i]!
    let splitEq ← proveSplittingsEq cfg splittings 0
    let mut fullEq := splitEq
    if tStop < stop then
      let afterStr ← concatStrs cfg ctx tStop stop
      let appendAfterFn ← withLocalDecl `_x .default cfg.stringTy fun x => do
        let bodyE ← mkAppM ``HAppend.hAppend #[x, afterStr]
        mkLambdaFVars #[x] bodyE
      fullEq ← mkAppM ``congrArg #[appendAfterFn, fullEq]
    for i in List.range (tStart - start) do
      let idx := tStart - 1 - i
      let prefixStr := (ctx.getV idx).strExpr
      let prependFn ← withLocalDecl `_x .default cfg.stringTy fun x => do
        let bodyE ← mkAppM ``HAppend.hAppend #[prefixStr, x]
        mkLambdaFVars #[x] bodyE
      fullEq ← mkAppM ``congrArg #[prependFn, fullEq]
    let fullEqLhs ← concatStrs cfg newCtx newStart (newStart + comps.size)
    let fullEqLhsFull ← if tStop < stop then do
      let afterStr ← concatStrs cfg ctx tStop stop
      mkAppM ``HAppend.hAppend #[fullEqLhs, afterStr]
    else pure fullEqLhs
    let mut finalFullEqLhs := fullEqLhsFull
    for i in List.range (tStart - start) do
      let idx := tStart - 1 - i
      finalFullEqLhs ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, finalFullEqLhs]
    if ← isDefEq actualStr finalFullEqLhs then
      let goalEq ← mkAppM ``congrArg #[goal, fullEq]
      mkAppM ``cast #[goalEq, branchExpr]
    else
      let assocEq ← proveStrEq actualStr finalFullEqLhs
      let assocGoalEq ← mkAppM ``congrArg #[goal, assocEq]
      let step1 ← mkAppM ``cast #[assocGoalEq, branchExpr]
      let goalEq ← mkAppM ``congrArg #[goal, fullEq]
      mkAppM ``cast #[goalEq, step1]

/-- Build a right-nested tensor grammar from a flattened constructor type.
    Used by both `fold` and NL-constructor application paths. -/
partial def buildTensorGram (cfg : ElabConfig) (ww : Expr) (body : Expr) : TermElabM Expr := do
  match body with
  | .forallE _ splitTy afterS _ =>
    let splitTyW ← whnf splitTy
    if !splitTyW.getAppFn.isConstOf ``Splitting then
      abstractGrammar ww body
    else
      let sVar ← mkFreshExprMVar (some splitTyW)
      let sLeft ← mkAppM ``Splitting.left #[sVar]
      let afterSInst := afterS.instantiate1 sVar
      match afterSInst with
      | .forallE _ leftTy rest _ =>
        let leftGram ← abstractGrammarReplace ww leftTy sLeft
        let dummy ← mkFreshExprMVar none
        let restBody := rest.instantiate1 dummy
        match restBody with
        | .forallE _ nextSplitTy _ _ =>
          let nextW ← whnf nextSplitTy
          if nextW.getAppFn.isConstOf ``Splitting then
            let sRight ← mkAppM ``Splitting.right #[sVar]
            let rightGram ← withLocalDecl `ww2 .default cfg.stringTy fun ww2 => do
              let restBody2 := restBody.replace fun e =>
                if e == sRight then some ww2 else none
              buildTensorGram cfg ww2 restBody2
            mkAppM ``GTensor #[leftGram, rightGram]
          else
            let sRight ← mkAppM ``Splitting.right #[sVar]
            let rightGram ← abstractGrammarReplace ww nextSplitTy sRight
            mkAppM ``GTensor #[leftGram, rightGram]
        | _ =>
          let sRight ← mkAppM ``Splitting.right #[sVar]
          let rightGram ← abstractGrammarReplace ww restBody sRight
          mkAppM ``GTensor #[leftGram, rightGram]
      | _ => throwError "unexpected tensor ctor shape"
  | _ => abstractGrammar ww body

end LambekD.Elab
