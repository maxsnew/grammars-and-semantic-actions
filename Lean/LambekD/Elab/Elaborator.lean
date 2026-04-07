import LambekD.Elab.Syntax
import LambekD.Elab.IDE
import LambekD.Elab.Match
import LambekD.Elab.Inductive

/-!
# The ordered linear term elaborator

The main `elaborateOrderedTerm` function and pattern elaboration for [| ... |].
-/

namespace LambekD.Elab

open Lean Elab Term Meta
open LambekD

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
    -- Base: s.eq : s.left ++ s.right = parent
    mkAppM ``Splitting.eq #[s]
  else
    -- Recursive: innerProof : innerConcat = s.right
    let innerProof ← proveSplittingsEq cfg splittings (idx + 1)
    -- congrArg (s.left ++ ·) innerProof : s.left ++ innerConcat = s.left ++ s.right
    let sLeft ← mkAppM ``Splitting.left #[s]
    let appendFn ← withLocalDecl `_x .default cfg.stringTy fun x => do
      let body ← mkAppM ``HAppend.hAppend #[sLeft, x]
      mkLambdaFVars #[x] body
    let congrProof ← mkAppM ``congrArg #[appendFn, innerProof]
    -- s.eq : s.left ++ s.right = parent
    let sEq ← mkAppM ``Splitting.eq #[s]
    -- trans : s.left ++ innerConcat = parent
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
            -- Elaborate the pattern to determine the constructor and pattern variables
            -- We build: fun (x : dom) => match x with | pattern => True
            -- and inspect the match to extract pattern info
            let patVarsAndCtor ← resolveNLPattern dom patternStx
            let (ctorIdx, patVarNames, patVarTypes) := patVarsAndCtor
            -- Introduce pattern variables
            let rec introPatVars (names : Array Name) (types : Array Expr) (i : Nat)
                (acc : Array Expr) (k' : Array Expr → TermElabM Expr) : TermElabM Expr := do
              if h : i < names.size then
                withLocalDecl names[i] .default types[i]! fun fv =>
                  introPatVars names types (i + 1) (acc.push fv) k'
              else k' acc
            introPatVars patVarNames patVarTypes 0 #[] fun patVarFvars => do
              -- Build the constructor expression from pattern vars
              let ctorExpr ← buildCtorExpr dom ctorIdx patVarFvars
              -- Instantiate ctor type with the constructor expression
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
    -- Look up ctor level params
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
    -- retArgs = params ++ extraIndices ++ [w]
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
private def hasStringBinder (cfg : ElabConfig) (cty : Expr) : TermElabM Bool := do
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

set_option maxHeartbeats 400000 in
partial def elaborateOrderedTerm
    (cfg : ElabConfig)
    (stx : TSyntax `gterm)
    (ctx : OrderedCtx)
    (start stop : Nat)
    (goal : Expr)
    (aliases : AliasMap := {})
    : TermElabM Expr := do
  withRef stx do
  -- Register linear context in info tree for IDE hover
  registerLinearCtxInfo stx ctx start stop aliases goal cfg.nlBinders
  match stx with

  -- ─── Variable ───────────────────────────────────────────
  | `(gterm| $x:ident) => do
    let name := x.getId
    -- Check alias map first (for product pattern variables)
    if let some alias := aliases.get? name then
      -- Resolve to the underlying ordered-context variable
      let ctxName := alias.ctxName
      let mut found : Option Nat := none
      for i in [start : stop] do
        if (ctx.getV i).userName == ctxName then
          found := some i
      match found with
      | none =>
        throwError "unbound linear variable '{name}' (alias for '{ctxName}')"
      | some idx =>
        if stop - start != 1 || idx != start then
          let unused := (List.range (stop - start)).map
            (fun i => (ctx.getV (start + i)).userName) |>.filter (· != ctxName)
          throwError "linear variable(s) {unused} unused when accessing '{name}'"
        let w := (ctx.getV idx).strExpr
        let gramW := mkApp alias.projGrammar w
        let goalW := mkApp goal w
        let ok ← isDefEq gramW goalW
        let ok ← if ok then pure true else do
          -- Retry with full reduction (handles computed indices like DyckAut.δ)
          let gramWR ← reduce gramW (explicitOnly := false) (skipTypes := false)
          let goalWR ← reduce goalW (explicitOnly := false) (skipTypes := false)
          isDefEq gramWR goalWR
        if ok then
          return alias.projExpr
        else
          throwError "variable '{name}' has grammar {← ppExpr alias.projGrammar} but expected {← ppExpr goal}"
    else
      let mut found : Option Nat := none
      for i in [start : stop] do
        if (ctx.getV i).userName == name then
          found := some i
      match found with
      | none =>
        throwError "unbound linear variable '{name}'"
      | some idx =>
        if stop - start != 1 || idx != start then
          let unused := (List.range (stop - start)).map
            (fun i => (ctx.getV (start + i)).userName) |>.filter (· != name)
          throwError "linear variable(s) {unused} unused when accessing '{name}'"
        let v := ctx.getV idx
        let w := v.strExpr
        let gramW := mkApp v.grammar w
        let goalW := mkApp goal w
        let ok ← isDefEq gramW goalW
        let ok ← if ok then pure true else do
          -- Retry with full reduction (handles computed indices like DyckAut.δ)
          let gramWR ← reduce gramW (explicitOnly := false) (skipTypes := false)
          let goalWR ← reduce goalW (explicitOnly := false) (skipTypes := false)
          isDefEq gramWR goalWR
        if ok then
          return v.parseExpr
        else
          throwError "variable '{name}' has grammar {← ppExpr v.grammar} but expected {← ppExpr goal}"

  -- ─── Epsilon ────────────────────────────────────────────
  | `(gterm| ε) => do
    if start != stop then
      let unused := (List.range (stop - start)).map (fun i => (ctx.getV (start + i)).userName)
      throwError "linear variable(s) {unused} unused in ε"
    let nil ← mkAppOptM ``List.nil #[some cfg.alphabetTy]
    let rflExpr ← mkAppOptM ``Eq.refl #[none, some nil]
    let plift ← mkAppM ``PLift.up #[rflExpr]
    mkAppM ``ULift.up #[plift]

  -- ─── Top ────────────────────────────────────────────────
  | `(gterm| tt) => do
    if start != stop then
      let unused := (List.range (stop - start)).map (fun i => (ctx.getV (start + i)).userName)
      throwError "linear variable(s) {unused} unused in tt"
    let punit := Lean.mkConst ``PUnit.unit
    mkAppM ``ULift.up #[punit]

  -- ─── Sorry ──────────────────────────────────────────────
  | `(gterm| sorry) => do
    let w ← concatStrs cfg ctx start stop
    mkSorry (mkApp goal w) (synthetic := true)

  -- ─── Tensor pair ────────────────────────────────────────
  | `(gterm| ($t₁, $t₂)) => do
    let (goalA, goalB) ← matchTensor cfg goal
    let k ← findSplit t₁ t₂ ctx start stop aliases (cfg.recInfo.map (·.recName))
    let e₁ ← elaborateOrderedTerm cfg t₁ ctx start k goalA aliases
    let e₂ ← elaborateOrderedTerm cfg t₂ ctx k stop goalB aliases
    let wLeft ← concatStrs cfg ctx start k
    let wRight ← concatStrs cfg ctx k stop
    let wFull ← concatStrs cfg ctx start stop
    let wLR ← mkAppM ``HAppend.hAppend #[wLeft, wRight]
    let rflExpr ← mkEqRefl wLR
    let sp ← mkAppOptM ``Splitting.mk #[none, none, some wLeft, some wRight, some rflExpr]
    -- Provide A, B explicitly to avoid mkAppM failing to infer through struct projection
    let tensor ← mkAppOptM ``Tensor.mk #[none, some goalA, some goalB, none, some sp, some e₁, some e₂]
    -- tensor : goal (wLeft ++ wRight). Cast to goal wFull if they differ.
    if ← isDefEq wLR wFull then
      return tensor
    else
      let strEq ← proveStrEq wLR wFull
      let goalEq ← mkAppM ``congrArg #[goal, strEq]
      mkAppM ``cast #[goalEq, tensor]

  -- ─── Let-tensor ─────────────────────────────────────────
  | `(gterm| let ($a:ident, $b:ident) = $t in $body) => do
    let (tStart, tStop) ← locateVars t ctx start stop aliases
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
    let mB ← mkFreshExprMVar (some gramTy) .natural `goalB
    let tGoal ← mkAppM ``Tensor #[mA, mB]
    let tExpr ← elaborateOrderedTerm cfg t ctx tStart tStop tGoal aliases
    let gramA ← instantiateMVars mA
    let gramB ← instantiateMVars mB
    let hasAfter := tStop < stop
    let wAfter ← concatStrs cfg ctx tStop stop
    let motiveC ← withLocalDecl `s .default cfg.stringTy fun s => do
      let mut fullStr := s
      if hasAfter then
        fullStr ← mkAppM ``HAppend.hAppend #[fullStr, wAfter]
      for i in List.range (tStart - start) do
        let idx := tStart - 1 - i
        fullStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, fullStr]
      mkLambdaFVars #[s] (mkApp goal fullStr)
    withLocalDecl `wL .default cfg.stringTy fun wL => do
    withLocalDecl `wR .default cfg.stringTy fun wR => do
      let aTy ← whnf (mkApp gramA wL)
      let bTy ← whnf (mkApp gramB wR)
      withLocalDecl a.getId .default aTy fun aVar => do
      withLocalDecl b.getId .default bTy fun bVar => do
        let aOV : OrderedVar := ⟨a.getId, gramA, wL, aVar⟩
        let bOV : OrderedVar := ⟨b.getId, gramB, wR, bVar⟩
        let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[aOV, bOV]
        let bodyExpr ← elaborateOrderedTerm cfg body newCtx newStart newStop goal aliases
        let finalBody ← if hasAfter then do
          let prefixFn ← if tStart > start then
            withLocalDecl `x .default cfg.stringTy fun x => do
              let mut result := x
              for i in List.range (tStart - start) do
                let idx := tStart - 1 - i
                result ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, result]
              mkLambdaFVars #[x] (mkApp goal result)
          else
            pure goal
          let assocProof ← mkAppM ``List.append_assoc #[wL, wR, wAfter]
          let congr ← mkAppM ``congrArg #[prefixFn, assocProof]
          mkAppM ``Eq.mpr #[congr, bodyExpr]
        else
          pure bodyExpr
        let bodyLam ← mkLambdaFVars #[wL, wR, aVar, bVar] finalBody
        mkAppM ``elimTensor #[motiveC, tExpr, bodyLam]

  -- ─── Let-unit ───────────────────────────────────────────
  | `(gterm| let ⟨⟩ = $t in $body) => do
    let (tStart, tStop) ← locateVars t ctx start stop aliases
    -- Build Epsilon grammar directly: fun w => ULift.{gramLevel,0} (PLift.{0} (w = []))
    -- Using explicit universe levels to avoid inference issues with mkAppM
    let epsConst ← withLocalDecl `_w .default cfg.stringTy fun ww => do
      let nilExpr ← mkAppOptM ``List.nil #[some cfg.alphabetTy]
      let eqTy ← mkEq ww nilExpr
      let pliftTy := mkApp (mkConst ``PLift [.zero]) eqTy
      let uliftTy := mkApp (mkConst ``ULift [cfg.gramLevel, .zero]) pliftTy
      mkLambdaFVars #[ww] uliftTy
    let tExpr ← elaborateOrderedTerm cfg t ctx tStart tStop epsConst aliases
    let wAfter ← concatStrs cfg ctx tStop stop
    let motiveC ← withLocalDecl `s .default cfg.stringTy fun s => do
      let mut fullStr := s
      if tStop < stop then
        fullStr ← mkAppM ``HAppend.hAppend #[fullStr, wAfter]
      for i in List.range (tStart - start) do
        let idx := tStart - 1 - i
        fullStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, fullStr]
      mkLambdaFVars #[s] (mkApp goal fullStr)
    let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[]
    let bodyExpr ← elaborateOrderedTerm cfg body newCtx newStart newStop goal aliases
    mkAppM ``elimEpsilon #[motiveC, tExpr, bodyExpr]

  -- ─── Let-unit (parentheses alias) ──────────────────────
  | `(gterm| let ( ) = $t in $body) => do
    let stx' ← `(gterm| let ⟨⟩ = $t in $body)
    elaborateOrderedTerm cfg stx' ctx start stop goal aliases

  -- ─── Right lambda ───────────────────────────────────────
  | `(gterm| fun ($x:ident : $tyStx) => $body) => do
    let (goalA, goalB) ← matchLinFunR goal
    let _tyExpr ← Lean.Elab.Term.elabTerm tyStx none
    withLocalDecl `w' .default cfg.stringTy fun wPrime => do
      let vTy ← whnf (mkApp goalA wPrime)
      withLocalDecl x.getId .default vTy fun vExpr => do
        let newVar : OrderedVar := ⟨x.getId, goalA, wPrime, vExpr⟩
        let newCtx := ctx[0:start].toArray ++ ctx[start:stop].toArray ++ #[newVar] ++ ctx[stop:ctx.size].toArray
        let bodyExpr ← elaborateOrderedTerm cfg body newCtx start (stop + 1) goalB aliases
        -- bodyExpr : goalB (concatStrs newCtx start (stop+1))
        -- Expected: goalB (concatStrs ctx start stop ++ wPrime)
        -- These may differ by associativity when context has ≥ 2 vars; cast if needed.
        let bodyExpr ← if stop - start >= 2 then do
          let actualStr ← concatStrs cfg newCtx start (stop + 1)
          let ctxStr ← concatStrs cfg ctx start stop
          let expectedStr ← mkAppM ``HAppend.hAppend #[ctxStr, wPrime]
          if ← isDefEq actualStr expectedStr then
            pure bodyExpr
          else
            let strEq ← proveStrEq actualStr expectedStr
            let goalEq ← mkAppM ``congrArg #[goalB, strEq]
            mkAppM ``cast #[goalEq, bodyExpr]
        else pure bodyExpr
        mkLambdaFVars #[wPrime, vExpr] bodyExpr

  -- ─── Left lambda ────────────────────────────────────────
  | `(gterm| funL ($x:ident : $tyStx) => $body) => do
    let (goalB, goalA) ← matchLinFunL goal
    let _tyExpr ← Lean.Elab.Term.elabTerm tyStx none
    withLocalDecl `w' .default cfg.stringTy fun wPrime => do
      let vTy ← whnf (mkApp goalA wPrime)
      withLocalDecl x.getId .default vTy fun vExpr => do
        let newVar : OrderedVar := ⟨x.getId, goalA, wPrime, vExpr⟩
        let newCtx := ctx[0:start].toArray ++ #[newVar] ++ ctx[start:stop].toArray ++ ctx[stop:ctx.size].toArray
        let bodyExpr ← elaborateOrderedTerm cfg body newCtx start (stop + 1) goalB aliases
        mkLambdaFVars #[wPrime, vExpr] bodyExpr

  -- ─── Application ────────────────────────────────────────
  | `(gterm| $f $a) => do
    -- Collect full application spine: `f a b c` (parsed as `(((f a) b) c)`) → `(head, #[a, b, c])`
    let appKind := stx.raw.getKind
    let rec collectSpine (s : Syntax) (acc : Array (TSyntax `gterm))
        : TSyntax `gterm × Array (TSyntax `gterm) :=
      if s.getKind == appKind && s.getNumArgs == 2 then
        collectSpine s[0] (#[⟨s[1]⟩] ++ acc)
      else
        (⟨s⟩, acc)
    let (head, allArgs) := collectSpine stx.raw #[]
    -- Check if head is an ident (potential constructor or external function)
    if let `(gterm| $c:ident) := head then
      let name := c.getId
      let isLinVar := (List.range (stop - start)).any fun i =>
        (ctx.getV (start + i)).userName == name
      let isAlias := aliases.contains name
      if !isLinVar && !isAlias then do
        -- Check for recursive call via `rec ... as f of`
        if let some ri := cfg.recInfo then
          if name == ri.recName then
            if allArgs.size != 1 then
              throwError "recursive call '{name}' expects exactly 1 argument (the sub-term)"
            let argStx := allArgs[0]!
            if let `(gterm| $v:ident) := argStx then
              if let some ihExpr := ri.ihMap.get? v.getId then
                return ihExpr
              else
                throwError "'{v.getId}' is not a recursive sub-term of the scrutinee"
            else
              throwError "recursive call argument must be a variable name"
        -- Try constructor (single-arg or multi-arg)
        if let some fullCtorName ← tryResolveCtorName cfg goal name then
          let some (ctyAfterParams, ctorConst, params) ← instantiateCtorFull cfg goal fullCtorName
            | throwError "cannot instantiate ctor '{fullCtorName}'"
          let nNonLin ← countNonLinearBinders cfg ctyAfterParams
          if nNonLin > 0 then
            -- ═══ Constructor with non-linear binders ═══
            let nSplittings ← countTensorSplittings cfg goal fullCtorName
            let isZeroComp ← isZeroComponentCtor cfg ctyAfterParams
            let nGramArgs := if isZeroComp then 0
                             else if nSplittings > 0 then nSplittings + 1
                             else 1
            let expectedArgs := nNonLin + nGramArgs
            if allArgs.size != expectedArgs then
              throwError "constructor '{name}' expects {expectedArgs} arguments ({nNonLin} non-linear + {nGramArgs} grammar), got {allArgs.size}"
            -- 1. Elaborate non-linear args as Lean terms (sequential, types may depend)
            let mut tyAfterNL := ctyAfterParams
            let mut nlExprs : Array Expr := #[]
            for i in [:nNonLin] do
              match tyAfterNL with
              | .forallE _ dom body _ =>
                let termStx ← gtermToTermSyntax allArgs[i]!
                let argExpr ← Lean.Elab.Term.elabTerm termStx (some dom)
                nlExprs := nlExprs.push argExpr
                tyAfterNL := body.instantiate1 argExpr
              | _ => throwError "unexpected ctor shape (expected forallE for non-linear binder {i})"
            -- tyAfterNL now starts with ∀ (w : String), ...
            let w ← concatStrs cfg ctx start stop
            if isZeroComp then
              -- 2a. Zero grammar components: auto-synthesize epsilon witness
              if start != stop then
                let unused := (List.range (stop - start)).map (fun i => (ctx.getV (start + i)).userName)
                throwError "constructor '{name}' takes no grammar arguments but linear variables {unused} remain"
              -- Extract the expected epsilon type from the ctor type
              let epsTy := match tyAfterNL with
                | .forallE _ _ afterW _ =>
                  let body := afterW.instantiate1 w
                  match body with
                  | .forallE _ argTy _ _ => argTy
                  | _ => mkApp (mkConst ``Epsilon [cfg.gramLevel]) w
                | _ => mkApp (mkConst ``Epsilon [cfg.gramLevel]) w
              -- Construct epsilon witness using Lean's elaborator for correct universes
              let epsWitness ← Lean.Elab.Term.elabTerm (← `(⟨⟨rfl⟩⟩)) (some epsTy)
              let mut result := ctorConst
              for p in params do result := mkApp result p
              for nl in nlExprs do result := mkApp result nl
              result := mkApp result w
              result := mkApp result epsWitness
              return result
            else
              -- 2b. Non-zero grammar components
              let isTensor := nSplittings > 0
              -- Build grammar arg syntax from remaining allArgs
              let gramArgStx ← if nGramArgs == 1 then
                pure allArgs[nNonLin]!
              else
                -- Build right-nested pair: (a₁, (a₂, (a₃, a₄)))
                let mut pairStx := allArgs[allArgs.size - 1]!
                for i in List.range (nGramArgs - 1) do
                  let idx := allArgs.size - 2 - i
                  pairStx ← `(gterm| ($(allArgs[idx]!), $pairStx))
                pure pairStx
              -- Extract argGram from tyAfterNL (same logic as fold path)
              let argGram ← withLocalDecl `ww .default cfg.stringTy fun ww => do
                let afterW := match tyAfterNL with
                  | .forallE _ _ b _ => b.instantiate1 ww
                  | _ => tyAfterNL
                if isTensor then
                  let rec buildNLTensorGram (body : Expr) : TermElabM Expr := do
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
                                buildNLTensorGram restBody2
                              mkAppM ``Tensor #[leftGram, rightGram]
                            else
                              let sRight ← mkAppM ``Splitting.right #[sVar]
                              let rightGram ← abstractGrammarReplace ww nextSplitTy sRight
                              mkAppM ``Tensor #[leftGram, rightGram]
                          | _ =>
                            let sRight ← mkAppM ``Splitting.right #[sVar]
                            let rightGram ← abstractGrammarReplace ww restBody sRight
                            mkAppM ``Tensor #[leftGram, rightGram]
                        | _ => throwError "unexpected tensor ctor shape"
                    | _ => abstractGrammar ww body
                  buildNLTensorGram afterW
                else
                  match afterW with
                  | .forallE _ argTy _ _ => abstractGrammar ww argTy
                  | _ => throwError "unexpected ctor shape"
              -- Elaborate the grammar arg
              let tExpr ← elaborateOrderedTerm cfg gramArgStx ctx start stop argGram aliases
              if isTensor then
                let afterW := match tyAfterNL with
                  | .forallE _ _ b _ => b.instantiate1 w
                  | _ => tyAfterNL
                let tensorArgs ← decomposeTensorForCtor tExpr afterW
                let allCtorArgs := params ++ nlExprs ++ #[w] ++ tensorArgs
                return ← mkAppOptM fullCtorName (allCtorArgs.map some)
              else
                let allCtorArgs := params ++ nlExprs ++ #[w, tExpr]
                return ← mkAppOptM fullCtorName (allCtorArgs.map some)
          else
            -- ═══ EXISTING PATH (nNonLin == 0) ═══
            if allArgs.size == 1 then
              let foldStx ← `(gterm| fold $c $(allArgs[0]!))
              return ← elaborateOrderedTerm cfg foldStx ctx start stop goal aliases
            else
              let nSplittings ← countTensorSplittings cfg goal fullCtorName
              if nSplittings == 0 then
                throwError "constructor '{name}' takes 1 argument, got {allArgs.size}"
              let expectedArgs := nSplittings + 1
              if allArgs.size != expectedArgs then
                throwError "constructor '{name}' expects {expectedArgs} arguments, got {allArgs.size}"
              let mut pairStx := allArgs[allArgs.size - 1]!
              for i in List.range (allArgs.size - 1) do
                let idx := allArgs.size - 2 - i
                pairStx ← `(gterm| ($(allArgs[idx]!), $pairStx))
              let foldStx ← `(gterm| fold $c $pairStx)
              return ← elaborateOrderedTerm cfg foldStx ctx start stop goal aliases
        -- Try external function (Lean-level definition with type A ⊢ B)
        else
          let s ← saveState
          let resolved ← try
            let gramTy ← mkGrammarTy cfg
            let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
            let fExpectedTy ← withLocalDecl `w .default cfg.stringTy fun w => do
              let aw ← whnf (mkApp mA w)
              let bw ← whnf (mkApp goal w)
              let fnBody ← mkArrow aw bw
              mkForallFVars #[w] fnBody
            let fExpr ← Lean.Elab.Term.elabTerm (← `($c)) (some fExpectedTy)
            let gramA ← instantiateMVars mA
            pure (some (fExpr, gramA))
          catch _ =>
            restoreState s
            pure none
          if let some (fExpr, gramA) := resolved then
            -- Build argument (single or multi-arg)
            let argStx ← if allArgs.size == 1 then
              pure allArgs[0]!
            else
              -- Multi-arg: build right-nested pair
              let mut p := allArgs[allArgs.size - 1]!
              for i in List.range (allArgs.size - 1) do
                let idx := allArgs.size - 2 - i
                p ← `(gterm| ($(allArgs[idx]!), $p))
              pure p
            let tExpr ← elaborateOrderedTerm cfg argStx ctx start stop gramA aliases
            let w ← concatStrs cfg ctx start stop
            return ← mkAppM' fExpr #[w, tExpr]
    -- Fall through: normal linear application (use original f and a)
    let fNames := collectAllIdents f
    let aNames := collectAllIdents a
    let mut fPositions : Array Nat := #[]
    let mut aPositions : Array Nat := #[]
    for i in [start : stop] do
      let name := (ctx.getV i).userName
      let inF := fNames.contains name
      let inA := aNames.contains name
      if inF && inA then
        throwError "linear variable '{name}' used in both function and argument (contraction)"
      if inF then fPositions := fPositions.push i
      if inA then aPositions := aPositions.push i
      if !inF && !inA then
        throwError "linear variable '{name}' unused in application (weakening)"
    let isRightApp : Bool := match fPositions.back?, aPositions[0]? with
      | some fm, some am => fm < am
      | _, none          => true
      | none, _          => false
    let gramTy ← mkGrammarTy cfg
    if isRightApp == true then
      let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
      let fGoal ← mkAppM ``FunctionR #[mA, goal]
      let k ← findSplit f a ctx start stop aliases
      let eF ← elaborateOrderedTerm cfg f ctx start k fGoal aliases
      let eA ← elaborateOrderedTerm cfg a ctx k stop mA aliases
      let wA ← concatStrs cfg ctx k stop
      let result ← mkAppM' eF #[wA, eA]
      let wF ← concatStrs cfg ctx start k
      let wFA ← mkAppM ``HAppend.hAppend #[wF, wA]
      let wFull ← concatStrs cfg ctx start stop
      if ← isDefEq wFA wFull then
        return result
      else
        let strEq ← proveStrEq wFA wFull
        let goalEq ← mkAppM ``congrArg #[goal, strEq]
        mkAppM ``cast #[goalEq, result]
    else
      let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
      let fGoal ← mkAppM ``FunctionL #[goal, mA]
      let k ← findSplit a f ctx start stop aliases
      let eA ← elaborateOrderedTerm cfg a ctx start k mA aliases
      let eF ← elaborateOrderedTerm cfg f ctx k stop fGoal aliases
      let wA ← concatStrs cfg ctx start k
      let result ← mkAppM' eF #[wA, eA]
      let wF ← concatStrs cfg ctx k stop
      let wAF ← mkAppM ``HAppend.hAppend #[wA, wF]
      let wFull ← concatStrs cfg ctx start stop
      if ← isDefEq wAF wFull then
        return result
      else
        let strEq ← proveStrEq wAF wFull
        let goalEq ← mkAppM ``congrArg #[goal, strEq]
        mkAppM ``cast #[goalEq, result]

  -- ─── Additive pair ──────────────────────────────────────
  | `(gterm| ⟨$t₁, $t₂⟩) => do
    let (goalA, goalB) ← matchProd cfg goal
    let e₁ ← elaborateOrderedTerm cfg t₁ ctx start stop goalA aliases
    let e₂ ← elaborateOrderedTerm cfg t₂ ctx start stop goalB aliases
    mkAppM ``Prod.mk #[e₁, e₂]

  -- ─── Projections ────────────────────────────────────────
  | `(gterm| fst $t) => do
    let gramTy ← mkGrammarTy cfg
    let mB ← mkFreshExprMVar (some gramTy) .natural `goalB
    let tGoal ← mkAppM ``Product #[goal, mB]
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop tGoal aliases
    mkAppM ``Prod.fst #[tExpr]

  | `(gterm| snd $t) => do
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
    let tGoal ← mkAppM ``Product #[mA, goal]
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop tGoal aliases
    mkAppM ``Prod.snd #[tExpr]

  -- ─── Injections ─────────────────────────────────────────
  | `(gterm| inl $t) => do
    let (goalA, goalB) ← matchSum cfg goal
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop goalA aliases
    let w ← concatStrs cfg ctx start stop
    let bw := mkApp goalB w
    mkAppOptM ``Sum.inl #[none, some bw, some tExpr]

  | `(gterm| inr $t) => do
    let (goalA, goalB) ← matchSum cfg goal
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop goalB aliases
    let w ← concatStrs cfg ctx start stop
    let aw := mkApp goalA w
    mkAppOptM ``Sum.inr #[some aw, none, some tExpr]

  -- ─── Case ───────────────────────────────────────────────
  | `(gterm| case $t of | inl $x:ident => $u₁ | inr $y:ident => $u₂) => do
    let (tStart, tStop) ← locateVars t ctx start stop aliases
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
    let mB ← mkFreshExprMVar (some gramTy) .natural `goalB
    let tGoal ← mkAppM ``Sum #[mA, mB]
    let tExpr ← elaborateOrderedTerm cfg t ctx tStart tStop tGoal aliases
    let gramA ← instantiateMVars mA
    let gramB ← instantiateMVars mB
    let wT ← concatStrs cfg ctx tStart tStop
    let aTy ← whnf (mkApp gramA wT)
    let bTy ← whnf (mkApp gramB wT)
    let u₁Lam ← withLocalDecl x.getId .default aTy fun aVar => do
      let aOV : OrderedVar := ⟨x.getId, gramA, wT, aVar⟩
      let (ctxL, startL, stopL) := replaceSlice ctx start stop tStart tStop #[aOV]
      let e ← elaborateOrderedTerm cfg u₁ ctxL startL stopL goal aliases
      mkLambdaFVars #[aVar] e
    let u₂Lam ← withLocalDecl y.getId .default bTy fun bVar => do
      let bOV : OrderedVar := ⟨y.getId, gramB, wT, bVar⟩
      let (ctxR, startR, stopR) := replaceSlice ctx start stop tStart tStop #[bOV]
      let e ← elaborateOrderedTerm cfg u₂ ctxR startR stopR goal aliases
      mkLambdaFVars #[bVar] e
    let w ← concatStrs cfg ctx start stop
    let goalW := mkApp goal w
    let sumTy ← whnf (← inferType tExpr)
    let motive := .lam `_ sumTy goalW .default
    mkAppOptM ``Sum.casesOn #[some aTy, some bTy, some motive, some tExpr, some u₁Lam, some u₂Lam]

  -- ─── Absurd ─────────────────────────────────────────────
  | `(gterm| absurd $t) => do
    let botConst ← mkAppM ``Bottom #[]
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop botConst aliases
    let tDown ← mkAppM ``ULift.down #[tExpr]
    mkAppM ``PEmpty.elim #[tDown]

  -- ─── Indexed product intro (Λ) ──────────────────────────
  | `(gterm| Λ ($x:ident : $tyStx) => $body) => do
    let (idxTy, fam) ← matchIdxProduct goal
    let _tyExpr ← Lean.Elab.Term.elabTerm tyStx (some idxTy)
    withLocalDecl x.getId .default idxTy fun xVar => do
      let bodyGoal := mkApp fam xVar
      let bodyExpr ← elaborateOrderedTerm cfg body ctx start stop bodyGoal aliases
      mkLambdaFVars #[xVar] bodyExpr

  -- ─── Indexed product elim (projection at index) ──────────
  | `(gterm| $t ⌈$idx⌉) => do
    let gramTy ← mkGrammarTy cfg
    let mGoal ← mkFreshExprMVar (some gramTy) .natural `tGoal
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop mGoal aliases
    let tGoal ← instantiateMVars mGoal
    let (idxTy, fam) ← matchIdxProduct tGoal
    let idxExpr ← Lean.Elab.Term.elabTerm idx (some idxTy)
    mkAppM' tExpr #[idxExpr]

  -- ─── Indexed coproduct intro (σ) ─────────────────────────
  | `(gterm| σ⟨$idx, $t⟩) => do
    let (idxTy, fam) ← matchIdxCoproduct goal
    let idxExpr ← Lean.Elab.Term.elabTerm idx (some idxTy)
    let bodyGoal := mkApp fam idxExpr
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop bodyGoal aliases
    let w ← concatStrs cfg ctx start stop
    -- β = fun x => fam x w
    let beta ← withLocalDecl `x .default idxTy fun xv => do
      mkLambdaFVars #[xv] (mkApp (mkApp fam xv) w)
    mkAppOptM ``Sigma.mk #[some idxTy, some beta, some idxExpr, some tExpr]

  -- ─── Indexed coproduct elim (caseDep) ────────────────────
  | `(gterm| caseDep $t of | σ⟨$x:ident, $y:ident⟩ => $body) => do
    let (tStart, tStop) ← locateVars t ctx start stop aliases
    let gramTy ← mkGrammarTy cfg
    let mGoal ← mkFreshExprMVar (some gramTy) .natural `tGoal
    let tExpr ← elaborateOrderedTerm cfg t ctx tStart tStop mGoal aliases
    let tGoalResolved ← instantiateMVars mGoal
    let (idxTy, fam) ← matchIdxCoproduct tGoalResolved
    let wT ← concatStrs cfg ctx tStart tStop
    withLocalDecl x.getId .default idxTy fun xVar => do
      let gramBody := mkApp fam xVar
      let bodyTy ← whnf (mkApp gramBody wT)
      withLocalDecl y.getId .default bodyTy fun yVar => do
        let yOV : OrderedVar := ⟨y.getId, gramBody, wT, yVar⟩
        let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[yOV]
        let branchExpr ← elaborateOrderedTerm cfg body newCtx newStart newStop goal aliases
        let branchLam ← mkLambdaFVars #[xVar, yVar] branchExpr
        let w ← concatStrs cfg ctx start stop
        let goalW := mkApp goal w
        let sumTy ← whnf (← inferType tExpr)
        let motive := .lam `_ sumTy goalW .default
        mkAppOptM ``Sigma.casesOn #[none, none, some motive, some tExpr, some branchLam]

  -- ─── Fold (inductive constructor) ─────────────────────────
  | `(gterm| fold $ctor:ident $t) => do
    let fullCtorName ← resolveCtorName cfg goal ctor.getId
    let isTensor ← isTensorCtor cfg goal fullCtorName
    let w ← concatStrs cfg ctx start stop
    -- Get ctor type with correct universe levels and params
    let some (ctyAfterParams, ctorConst, params) ← instantiateCtorFull cfg goal fullCtorName
      | throwError "cannot instantiate ctor '{fullCtorName}'"
    -- Guard: fold doesn't support constructors with non-linear binders
    let nNonLin ← countNonLinearBinders cfg ctyAfterParams
    if nNonLin > 0 then
      throwError "constructor '{ctor.getId}' has {nNonLin} non-linear parameter(s); use multi-arg syntax (e.g., '{ctor.getId} arg₁ arg₂ ...') instead of 'fold'"
    -- ctyAfterParams: ∀ (w : String), ... → RetTy w
    -- Extract the argument grammar from the ctor type so universe levels match exactly
    let argGram ← withLocalDecl `ww .default cfg.stringTy fun ww => do
      let afterW := match ctyAfterParams with
        | .forallE _ _ b _ => b.instantiate1 ww
        | _ => ctyAfterParams
      if isTensor then
        -- Reconstruct the tensor grammar from the flattened ctor type
        let rec buildTensorGram (body : Expr) : TermElabM Expr := do
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
                      buildTensorGram restBody2
                    mkAppM ``Tensor #[leftGram, rightGram]
                  else
                    let sRight ← mkAppM ``Splitting.right #[sVar]
                    let rightGram ← abstractGrammarReplace ww nextSplitTy sRight
                    mkAppM ``Tensor #[leftGram, rightGram]
                | _ =>
                  let sRight ← mkAppM ``Splitting.right #[sVar]
                  let rightGram ← abstractGrammarReplace ww restBody sRight
                  mkAppM ``Tensor #[leftGram, rightGram]
              | _ => throwError "unexpected tensor ctor shape in fold"
          | _ => abstractGrammar ww body
        buildTensorGram afterW
      else
        -- Simple ctor: ∀ (w : String), ArgTy w → RetTy w
        match afterW with
        | .forallE _ argTy _ _ =>
          abstractGrammar ww argTy
        | _ => throwError "unexpected simple ctor shape in fold"
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop argGram aliases
    if isTensor then
      -- Decompose the tensor value for the flattened ctor args
      let afterW := match ctyAfterParams with
        | .forallE _ _ b _ => b.instantiate1 w
        | _ => ctyAfterParams
      let tensorArgs ← decomposeTensorForCtor tExpr afterW
      let mut result := ctorConst
      for p in params do
        result := mkApp result p
      result := mkApp result w
      for ta in tensorArgs do
        result := mkApp result ta
      return result
    else
      let mut result := ctorConst
      for p in params do
        result := mkApp result p
      result := mkApp result w
      result := mkApp result tExpr
      return result

  -- ─── Escape hatch ───────────────────────────────────────
  | `(gterm| #[ $f ] $t) => do
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
    let fExpectedTy ← withLocalDecl `w .default cfg.stringTy fun w => do
      let aw ← whnf (mkApp mA w)
      let bw ← whnf (mkApp goal w)
      let body ← mkArrow aw bw
      mkForallFVars #[w] body
    let fExpr ← Lean.Elab.Term.elabTerm f (some fExpectedTy)
    let gramA ← instantiateMVars mA
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop gramA aliases
    let w ← concatStrs cfg ctx start stop
    mkAppM' fExpr #[w, tExpr]

  | `(gterm| ($t)) => elaborateOrderedTerm cfg t ctx start stop goal aliases

  -- ─── Rec (inductive elimination) ──────────────────────────
  -- Matched by raw syntax since `$[...]*` repetition doesn't work in gterm patterns
  | stx => do
    let isCaseInd := stx.raw.getKind == `caseIndGterm || stx.raw.getKind == `LambekD.Elab.caseIndGterm
    if isCaseInd || stx.raw.getKind == `recGterm || stx.raw.getKind == `LambekD.Elab.recGterm then
      let t : TSyntax `gterm := ⟨stx.raw[1]⟩
      -- Parse optional "as ident" for recursive elimination via .rec (only for rec syntax)
      let (recName?, branches) := if isCaseInd then
        (none, stx.raw[3].getArgs)
      else
        let asGroup := stx.raw[2]
        let rn : Option Name := if asGroup.getNumArgs >= 2 then some asGroup[1].getId else none
        (rn, stx.raw[4].getArgs)
      let (tStart, tStop) ← locateVars t ctx start stop aliases
      let gramTy ← mkGrammarTy cfg
      let mGoal ← mkFreshExprMVar (some gramTy) .natural `tGoal
      let tExpr ← elaborateOrderedTerm cfg t ctx tStart tStop mGoal aliases
      let tGoalResolved ← instantiateMVars mGoal
      -- When the input and output grammars are the same inductive (e.g., StarG A ⊢ StarG A),
      -- unify their universe levels to avoid mismatches in casesOn branches.
      try let _ ← isDefEq tGoalResolved goal catch _ => pure ()
      let tGoalResolved ← instantiateMVars tGoalResolved
      let wT ← concatStrs cfg ctx tStart tStop
      -- Get the inductive type info
      let tGoalW ← whnf (mkApp tGoalResolved wT)
      let indName := tGoalW.getAppFn.constName!
      let env ← getEnv
      let some indVal := getInductiveVal env indName
        | throwError "'{indName}' is not an inductive type"
      let numParams := indVal.numParams
      let allArgs := tGoalW.getAppArgs
      let paramsOnly := allArgs[:numParams]
      -- Detect extra indices (indices beyond w : String)
      let numExtraIndices := indVal.numIndices - 1
      let extraIdxArgs := allArgs[numParams : numParams + numExtraIndices].toArray
      -- Get the inductive type's universe levels for motive construction
      let indLevels := tGoalW.getAppFn.constLevels!
      -- Motive: fun (idx₁ : T₁) ... (idxₖ : Tₖ) (w_mot : String) (_ : IndTy idx... w_mot) => body
      -- For casesOn: body = ∀ (h_idx₁ : idx₁ = orig₁) ... (h_w : w_mot = wT), goal(...)
      -- For rec: body = goal(...)
      let motive ← do
        -- Get index binder types from the inductive's type
        let some indInfo := env.find? indName
          | throwError "'{indName}' not found in environment"
        let indType := indInfo.type.instantiateLevelParams indInfo.levelParams indLevels
        let mut tyAfterParams := indType
        for p in paramsOnly do
          match tyAfterParams with
          | .forallE _ _ body _ => tyAfterParams := body.instantiate1 p
          | _ => throwError "unexpected inductive type shape"
        -- Build motive with extra index binders via CPS
        withMotiveIdxBinders tyAfterParams numExtraIndices #[] fun idxFvars => do
          withLocalDecl `w_mot .default cfg.stringTy fun wMot => do
            -- Build IndTy applied to idxFvars and wMot
            let mut indApp := Lean.mkConst indName indLevels
            for p in paramsOnly do indApp := mkApp indApp p
            for fv in idxFvars do indApp := mkApp indApp fv
            indApp := mkApp indApp wMot
            let indTyMot ← whnf indApp
            withLocalDecl `t_mot .default indTyMot fun tMot => do
              -- Build full string with wMot replacing scrutinee's portion
              let mut motiveStr := wMot
              if tStop < stop then
                let afterStr ← concatStrs cfg ctx tStop stop
                motiveStr ← mkAppM ``HAppend.hAppend #[motiveStr, afterStr]
              for i in List.range (tStart - start) do
                let idx := tStart - 1 - i
                motiveStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, motiveStr]
              let goalBody := mkApp goal motiveStr
              let motiveBody ← if recName?.isNone then do
                -- casesOn: add equality foralls for w and extra indices
                let mut body := goalBody
                let eqTyW ← mkEq wMot wT
                body := Expr.forallE `_h_w eqTyW body .default
                for i in List.range numExtraIndices do
                  let j := numExtraIndices - 1 - i
                  let eqTy ← mkEq idxFvars[j]! extraIdxArgs[j]!
                  body := Expr.forallE (Name.mkSimple s!"_h_idx_{j}") eqTy body .default
                pure body
              else pure goalBody
              mkLambdaFVars (idxFvars ++ #[wMot, tMot]) motiveBody
      -- Helper: instantiate ctor type with params, returning the remaining type
      let instantiateCtorParams (fullCtorName : Name) : TermElabM Expr := do
        let some ci := env.find? fullCtorName
          | throwError "constructor '{fullCtorName}' not found"
        let ctorInst := ci.type.instantiateLevelParams ci.levelParams
          (tGoalW.getAppFn.constLevels!)
        let mut cty := ctorInst
        for p in paramsOnly do
          match cty with
          | .forallE _ _ b _ => cty := b.instantiate1 p
          | _ => throwError "unexpected ctor shape"
        return cty
      -- Validate and group branches by constructor
      let ctorShortNames := indVal.ctors.map fun n => n.replacePrefix indName .anonymous
      let ctorList := ", ".intercalate (ctorShortNames.map (·.toString))
      -- Validate all branch names and group by constructor (preserving order)
      let mut branchGroups : Std.HashMap Name (Array Syntax) := {}
      let mut lastCtorIdx : Int := -1
      for b in branches do
        let bname := b[1].getId
        let some ctorIdx := ctorShortNames.findIdx? (· == bname)
          | throwErrorAt b[1] "'{bname}' is not a constructor of '{indName}'; constructors are: {ctorList}"
        -- Check ordering: constructors must appear in declaration order (groups are consecutive)
        if branchGroups.contains bname then
          -- Same ctor again: must be consecutive (lastCtorIdx must match)
          if lastCtorIdx != ctorIdx then
            throwErrorAt b[1] "branches for '{bname}' must be consecutive"
        else
          -- New ctor: must come after all previous ones
          if ctorIdx < lastCtorIdx then
            throwErrorAt b[1] "branch '{bname}' is out of order (branches must match constructor order)"
        lastCtorIdx := ctorIdx
        branchGroups := branchGroups.insert bname
          ((branchGroups.getD bname #[]).push b)
      -- Check all constructors are covered
      for cn in ctorShortNames do
        unless branchGroups.contains cn do
          throwError "missing branch for constructor '{cn}'; constructors are: {ctorList}"
      -- Build branch lambdas for each constructor (one lambda per constructor)
      let mut branchLams : Array Expr := #[]
      for fullCtorName in indVal.ctors do
        let ctorName := fullCtorName.replacePrefix indName .anonymous
        let group := branchGroups.getD ctorName #[]
        let branch := group[0]!  -- representative branch for shared ctor info
        let varNodes := branch[2].getArgs
        let isTensor ← isTensorCtor cfg tGoalResolved fullCtorName
        let cty ← instantiateCtorParams fullCtorName
        let hasW ← hasStringBinder cfg cty
        let nNonLin ← if hasW then countNonLinearBinders cfg cty else pure 0
        -- Parse NL binder infos and grammar var idents from the representative branch
        let nlBinderInfos := (varNodes[:nNonLin].toArray).mapIdx fun i s => parseGBranchVar s i
        let gramVarNodes := varNodes[nNonLin:].toArray
        let gramVarIdents ← gramVarNodes.mapM fun s => do
          if s.isIdent then pure s
          else if s.getNumArgs == 1 && s[0].isIdent then pure s[0]
          else if s.getNumArgs >= 3 && s[1].isIdent then pure s[1]
          else throwError "patterns only allowed in non-linear positions, not grammar positions"
        -- Check for NL patterns + rec (not yet supported)
        let hasNLPatterns := nlBinderInfos.any fun | .pattern .. => true | _ => false
        if hasNLPatterns && recName?.isSome then
          throwError "NL patterns + rec not yet supported"
        if group.size > 1 && recName?.isSome then
          throwError "multi-branch NL patterns + rec not yet supported"
        -- ─── Multi-branch path: merge sub-branches via NL casesOn ───
        let lam ← if group.size > 1 then do
          -- All sub-branches share the same NL binder count.
          -- Introduce NL binders as raw idents (no pattern matching).
          let nlNames := nlBinderInfos.map fun | .ident n => n | .pattern n _ => n
          withNonLinearBranchBinders cfg cty nlNames nNonLin 0 #[] fun nlFvars tyFromW => do
          let cfgNL := { cfg with nlBinders := cfg.nlBinders ++ nlFvars }
          -- Find which NL binder position is split (has different patterns across sub-branches)
          let mut splitIdx : Option Nat := none
          for i in [:nNonLin] do
            let pats := group.map fun b => parseGBranchVar b[2].getArgs[i]! i
            let allSame := pats.all fun p => match p, pats[0]! with
              | .ident n1, .ident n2 => n1 == n2
              | _, _ => false
            if !allSame then
              splitIdx := some i
              break
          let some splitPos := splitIdx
            | throwError "multi-branch group for '{ctorName}' but no NL binder differs between branches"
          let splitFvar := nlFvars[splitPos]!
          let splitTy ← whnf (← inferType splitFvar)
          let splitIndName := splitTy.getAppFn.constName!
          let some splitIndVal := getInductiveVal env splitIndName
            | throwError "NL binder type '{splitIndName}' is not an inductive type"
          -- For each sub-branch, resolve its NL pattern for the split binder and elaborate body
          let mut armMap : Std.HashMap Nat Expr := {}
          for subBranch in group do
            let subVarNodes := subBranch[2].getArgs
            let subBody : TSyntax `gterm := ⟨subBranch[4]⟩
            let subPatStx := subVarNodes[splitPos]!
            let patInfo := parseGBranchVar subPatStx splitPos
            let patSyntax ← match patInfo with
              | .pattern _ stx => pure stx
              | .ident n => pure (Lean.mkIdent n : Syntax)
            let (subCtorIdx, patVarNames, patVarTypes) ←
              resolveNLPattern splitTy patSyntax
            -- Introduce pattern variables, elaborate body, collect arm.
            -- The arm lambda already has patVars abstracted (via mkLambdaFVars).
            let armLam ← withPatternVarDecls patVarNames patVarTypes 0 #[] fun patFvars => do
              let cfgSub := { cfgNL with nlBinders := cfgNL.nlBinders ++ patFvars }
              let innerBody ← withLocalDecl `w_br .default cfg.stringTy fun wBr => do
                match tyFromW with
                | .forallE _ _ afterW _ =>
                  let afterWInst := afterW.instantiate1 wBr
                  let branchIdxExprs ← extractBranchIndexExprs tyFromW wBr numParams numExtraIndices
                  let mut eqInfos : Array (Name × Expr) := #[]
                  for j in [:numExtraIndices] do
                    let eqTy ← mkEq branchIdxExprs[j]! extraIdxArgs[j]!
                    eqInfos := eqInfos.push (Name.mkSimple s!"_h_idx_{j}", eqTy)
                  let eqTyW ← mkEq wBr wT
                  eqInfos := eqInfos.push (`_h_w, eqTyW)
                  if isTensor && gramVarIdents.size > 1 then
                    withTensorCtorComponents cfg afterWInst fun fvars comps => do
                      let names' := gramVarIdents.map (·.getId)
                      if names'.size != comps.size then
                        throwError "constructor '{ctorName}' has {comps.size} fields but pattern has {names'.size} variables"
                      let mut componentOVs : Array OrderedVar := #[]
                      for j in [:comps.size] do
                        let (gram, str, parse) := comps[j]!
                        componentOVs := componentOVs.push ⟨names'[j]!, gram, str, parse⟩
                      let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop componentOVs
                      let branchExpr ← elaborateOrderedTerm cfgSub subBody newCtx newStart newStop goal aliases
                      withEqBinders eqInfos 0 #[] fun eqFvars => do
                        mkLambdaFVars (#[wBr] ++ fvars ++ eqFvars) branchExpr
                  else
                    if gramVarIdents.size != 1 then
                      throwError "non-tensor constructor '{ctorName}' takes 1 argument, but pattern has {gramVarIdents.size} variables"
                    let varName' := gramVarIdents[0]!.getId
                    match afterWInst with
                    | .forallE _ argTy _ _ =>
                      let argGrammar ← withLocalDecl `ww .default cfg.stringTy fun ww => do
                        abstractGrammarReplace ww argTy wBr
                      withLocalDecl varName' .default argTy fun argVar => do
                        let argOV : OrderedVar := ⟨varName', argGrammar, wBr, argVar⟩
                        let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[argOV]
                        let branchExpr ← elaborateOrderedTerm cfgSub subBody newCtx newStart newStop goal aliases
                        withEqBinders eqInfos 0 #[] fun eqFvars => do
                          mkLambdaFVars (#[wBr, argVar] ++ eqFvars) branchExpr
                    | _ => throwError "unexpected ctor shape"
                | _ => throwError "unexpected ctor shape (no w binder)"
              -- Abstract pattern vars to form the casesOn arm lambda
              mkLambdaFVars patFvars innerBody
            if armMap.contains subCtorIdx then
              throwError "duplicate NL pattern for the same constructor of '{splitIndName}'"
            armMap := armMap.insert subCtorIdx armLam
          -- Verify all constructors of the split type are covered
          for (_, i) in splitIndVal.ctors.zipIdx.toArray do
            unless armMap.contains i do
              let missing := splitIndVal.ctors[i]!.replacePrefix splitIndName .anonymous
              throwError "missing NL pattern branch for '{missing}' of type '{splitIndName}'"
          -- Build the arms array in constructor order
          let mut arms : Array Expr := #[]
          for (_, i) in splitIndVal.ctors.zipIdx.toArray do
            arms := arms.push armMap[i]!
          -- Compute body type by peeling foralls from the first arm's type
          let bodyTy ← forallTelescopeReducing (← inferType arms[0]!) fun _ b => pure b
          -- Build casesOn on the split NL binder
          let matchExpr ← wrapWithNLMatchAll splitFvar bodyTy arms
          mkLambdaFVars nlFvars matchExpr
        else do
          -- ─── Single-branch path (existing logic) ───
          let nlNames := nlBinderInfos.map fun | .ident n => n | .pattern n _ => n
          let body : TSyntax `gterm := ⟨branch[4]⟩
          withNonLinearBranchBindersExt cfg cty nlBinderInfos nNonLin 0 #[] #[] fun nlFvars patInfos tyFromW => do
          let allPatVarFvars := patInfos.flatMap (·.patVarFvars)
          let cfgNL := { cfg with nlBinders := cfg.nlBinders ++ nlFvars ++ allPatVarFvars }
          -- Helper: wrap expression in NL pattern casesOn matches (no-op if no patterns)
          let wrapNLPatterns (e : Expr) : TermElabM Expr := do
            let mut wrapped := e
            for pi in patInfos.reverse do
              wrapped ← wrapWithNLMatch pi.nlFvar pi.patVarFvars pi.ctorIdx wrapped
            return wrapped
          withLocalDecl `w_br .default cfg.stringTy fun wBr => do
            match tyFromW with
            | .forallE _ _ afterW _ =>
              let afterWInst := afterW.instantiate1 wBr
              -- Extract branch's extra index expressions from ctor return type
              let branchIdxExprs ← extractBranchIndexExprs tyFromW wBr numParams numExtraIndices
              -- Helper: build full motive application (motive idx₁...idxₖ w t)
              let mkMotiveApp (gram str parse : Expr) : TermElabM Expr := do
                let mut app := motive
                if numExtraIndices > 0 then
                  let gramW ← whnf (mkApp gram str)
                  let gramArgs := gramW.getAppArgs
                  for j in [:numExtraIndices] do
                    app := mkApp app gramArgs[numParams + j]!
                app := mkApp (mkApp app str) parse
                return app
              if let some recName := recName? then
                -- ═══ .rec path: branches include IH binders ═══
                if isTensor && gramVarIdents.size > 1 then
                  -- Multi-arity tensor pattern with .rec
                  withTensorCtorComponents cfg afterWInst fun fvars comps => do
                    let names := gramVarIdents.map (·.getId)
                    if names.size != comps.size then
                      throwError "constructor '{ctorName}' has {comps.size} fields but pattern has {names.size} variables"
                    -- Build ordered vars from components
                    let mut componentOVs : Array OrderedVar := #[]
                    for i in [:comps.size] do
                      let (gram, str, parse) := comps[i]!
                      componentOVs := componentOVs.push ⟨names[i]!, gram, str, parse⟩
                    let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop componentOVs
                    -- Identify recursive components and collect IH info
                    let mut ihInfos : Array (Name × Expr) := #[]
                    for i in [:comps.size] do
                      let (gram, str, parse) := comps[i]!
                      let isRec ← isRecursiveComponent cfg indName gram
                      if isRec then
                        let ihTy ← mkMotiveApp gram str parse
                        ihInfos := ihInfos.push (names[i]!, ihTy)
                    -- CPS-introduce IH binders, elaborate body, build lambda
                    withRecIHBinders ihInfos 0 #[] {} fun ihFvars ihMap => do
                      let ri : RecCallInfo := ⟨recName, ihMap⟩
                      let cfgRec := { cfgNL with recInfo := some ri }
                      let branchExpr ← elaborateOrderedTerm cfgRec body newCtx newStart newStop goal aliases
                      -- Cast from goal(componentConcat ++ after) to goal(wBr ++ after)
                      -- The body uses component strings (s.left, s.right) but .rec expects wBr.
                      let actualStr ← concatStrs cfg newCtx newStart newStop
                      let mut motiveResultStr := wBr
                      if tStop < stop then
                        let afterStr ← concatStrs cfg ctx tStop stop
                        motiveResultStr ← mkAppM ``HAppend.hAppend #[motiveResultStr, afterStr]
                      for i in List.range (tStart - start) do
                        let idx := tStart - 1 - i
                        motiveResultStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, motiveResultStr]
                      let branchExpr ← if ← isDefEq actualStr motiveResultStr then
                        pure branchExpr
                      else
                        -- Build proof: componentConcat = wBr using splitting equalities
                        let splittings := (List.range ((comps.size - 1))).toArray.map
                          fun i => fvars[2 * i]!
                        let splitEq ← proveSplittingsEq cfg splittings 0
                        -- Extend to full string proof with before/after context
                        let mut fullEq := splitEq
                        if tStop < stop then
                          let afterStr ← concatStrs cfg ctx tStop stop
                          let appendAfterFn ← withLocalDecl `_x .default cfg.stringTy fun x => do
                            let body ← mkAppM ``HAppend.hAppend #[x, afterStr]
                            mkLambdaFVars #[x] body
                          fullEq ← mkAppM ``congrArg #[appendAfterFn, fullEq]
                        for i in List.range (tStart - start) do
                          let idx := tStart - 1 - i
                          let prefixStr := (ctx.getV idx).strExpr
                          let prependFn ← withLocalDecl `_x .default cfg.stringTy fun x => do
                            let body ← mkAppM ``HAppend.hAppend #[prefixStr, x]
                            mkLambdaFVars #[x] body
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
                      mkLambdaFVars (nlFvars ++ #[wBr] ++ fvars ++ ihFvars) branchExpr
                else if isTensor then
                  -- Single-arity tensor with .rec: error, require multi-arity
                  throwError "rec ... as: tensor constructor '{ctorName}' requires multi-arity pattern to access induction hypotheses (use '| {ctorName} x₁ x₂ ... =>' instead)"
                else
                  -- Non-tensor with .rec: single argument, may or may not be recursive
                  if gramVarIdents.size != 1 then
                    throwError "non-tensor constructor '{ctorName}' takes 1 argument, but pattern has {gramVarIdents.size} variables"
                  let varName := gramVarIdents[0]!.getId
                  match afterWInst with
                  | .forallE _ argTy _ _ =>
                    let argGrammar ← withLocalDecl `ww .default cfg.stringTy fun ww => do
                      abstractGrammarReplace ww argTy wBr
                    withLocalDecl varName .default argTy fun argVar => do
                      let argOV : OrderedVar := ⟨varName, argGrammar, wBr, argVar⟩
                      let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[argOV]
                      -- Check if this argument is recursive
                      let isRec ← isRecursiveComponent cfg indName argGrammar
                      if isRec then
                        let ihTy ← mkMotiveApp argGrammar wBr argVar
                        let ihDeclName := Name.mkSimple s!"_ih_{varName}"
                        withLocalDecl ihDeclName .default ihTy fun ihVar => do
                          let ri : RecCallInfo := ⟨recName, ({} : Std.HashMap Name Expr).insert varName ihVar⟩
                          let cfgRec := { cfgNL with recInfo := some ri }
                          let branchExpr ← elaborateOrderedTerm cfgRec body newCtx newStart newStop goal aliases
                          mkLambdaFVars (nlFvars ++ #[wBr, argVar, ihVar]) branchExpr
                      else
                        -- Non-recursive argument: no IH, same as casesOn
                        let ri : RecCallInfo := ⟨recName, {}⟩
                        let cfgRec := { cfgNL with recInfo := some ri }
                        let branchExpr ← elaborateOrderedTerm cfgRec body newCtx newStart newStop goal aliases
                        mkLambdaFVars (nlFvars ++ #[wBr, argVar]) branchExpr
                  | _ => throwError "unexpected ctor shape"
              else
                -- ═══ .casesOn path ═══
                -- Build extra index + w equality info for casesOn branches
                let mut eqInfos : Array (Name × Expr) := #[]
                for i in [:numExtraIndices] do
                  let eqTy ← mkEq branchIdxExprs[i]! extraIdxArgs[i]!
                  eqInfos := eqInfos.push (Name.mkSimple s!"_h_idx_{i}", eqTy)
                let eqTyW ← mkEq wBr wT
                eqInfos := eqInfos.push (`_h_w, eqTyW)
                if isTensor && gramVarIdents.size > 1 then
                  -- Multi-arity pattern: place components directly (no elimTensor roundtrip)
                  -- so structural recursion checker can trace sub-terms through casesOn.
                  withTensorCtorComponents cfg afterWInst fun fvars comps => do
                    let names := gramVarIdents.map (·.getId)
                    if names.size != comps.size then
                      throwError "constructor '{ctorName}' has {comps.size} fields but pattern has {names.size} variables"
                    let mut componentOVs : Array OrderedVar := #[]
                    for i in [:comps.size] do
                      let (gram, str, parse) := comps[i]!
                      componentOVs := componentOVs.push ⟨names[i]!, gram, str, parse⟩
                    let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop componentOVs
                    let branchExpr ← elaborateOrderedTerm cfgNL body newCtx newStart newStop goal aliases
                    -- Cast from goal(componentConcat) to goal(wBr) if they differ
                    let actualStr ← concatStrs cfg newCtx newStart newStop
                    let mut motiveResultStr := wBr
                    if tStop < stop then
                      let afterStr ← concatStrs cfg ctx tStop stop
                      motiveResultStr ← mkAppM ``HAppend.hAppend #[motiveResultStr, afterStr]
                    for i in List.range (tStart - start) do
                      let idx := tStart - 1 - i
                      motiveResultStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, motiveResultStr]
                    let branchExpr ← if ← isDefEq actualStr motiveResultStr then
                      pure branchExpr
                    else
                      -- Build splitting equality proof: componentConcat = wBr
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
                    -- Add Literal/Epsilon length let-bindings for WF termination
                    let mut enrichedExpr := branchExpr
                    for i in [:comps.size] do
                      let (gram, _str, parse) := comps[i]!
                      if gram.isAppOf ``Literal then
                        let proof ← mkAppM ``Literal.length_eq #[parse]
                        let proofTy ← inferType proof
                        enrichedExpr ← withLetDecl (.mkSimple s!"_h_len_{i}") proofTy proof fun h =>
                          mkLetFVars #[h] enrichedExpr (usedLetOnly := false)
                      else if gram.isAppOf ``Epsilon then
                        let proof ← mkAppM ``Epsilon.length_eq #[parse]
                        let proofTy ← inferType proof
                        enrichedExpr ← withLetDecl (.mkSimple s!"_h_len_{i}") proofTy proof fun h =>
                          mkLetFVars #[h] enrichedExpr (usedLetOnly := false)
                    -- Add equality parameters for WF termination
                    let finalExpr ← wrapNLPatterns enrichedExpr
                    withEqBinders eqInfos 0 #[] fun eqFvars => do
                      mkLambdaFVars (nlFvars ++ #[wBr] ++ fvars ++ eqFvars) finalExpr
                else if isTensor then
                  -- Single-var tensor pattern
                  let varName := gramVarIdents[0]!.getId
                  withTensorCtorBinders cfg afterWInst fun fvars tensorVal tensorGram => do
                    let tensorOV : OrderedVar := ⟨varName, tensorGram, wBr, tensorVal⟩
                    let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[tensorOV]
                    let branchExpr ← elaborateOrderedTerm cfgNL body newCtx newStart newStop goal aliases
                    let branchExpr ← wrapNLPatterns branchExpr
                    withEqBinders eqInfos 0 #[] fun eqFvars => do
                      mkLambdaFVars (nlFvars ++ #[wBr] ++ fvars ++ eqFvars) branchExpr
                else
                  -- Simple: ArgTy w → IndTy w
                  if gramVarIdents.size != 1 then
                    throwError "non-tensor constructor '{ctorName}' takes 1 argument, but pattern has {gramVarIdents.size} variables"
                  let varName := gramVarIdents[0]!.getId
                  match afterWInst with
                  | .forallE _ argTy _ _ =>
                    let argGrammar ← withLocalDecl `ww .default cfg.stringTy fun ww => do
                      abstractGrammarReplace ww argTy wBr
                    withLocalDecl varName .default argTy fun argVar => do
                      let argOV : OrderedVar := ⟨varName, argGrammar, wBr, argVar⟩
                      let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[argOV]
                      let branchExpr ← elaborateOrderedTerm cfgNL body newCtx newStart newStop goal aliases
                      let branchExpr ← wrapNLPatterns branchExpr
                      withEqBinders eqInfos 0 #[] fun eqFvars => do
                        mkLambdaFVars (nlFvars ++ #[wBr, argVar] ++ eqFvars) branchExpr
                  | _ => throwError "unexpected ctor shape"
            | _ => throwError "unexpected ctor shape (no w binder)"
        branchLams := branchLams.push lam
      -- Apply .rec or .casesOn depending on whether `as` was specified
      let elimResult ← if recName?.isSome then do
        -- .rec signature: {params...} → {motive} → branches... → {idx₁}...{idxₖ} → {w} → (target) → motive ...
        let recFnName := indName ++ `rec
        let mut args : Array (Option Expr) := paramsOnly.toArray.map some
        args := args.push (some motive)
        for lam in branchLams do
          args := args.push (some lam)
        for _ in [:numExtraIndices] do
          args := args.push none         -- extra index (inferred)
        args := args.push none           -- w index (inferred)
        args := args.push (some tExpr)   -- target
        mkAppOptM recFnName args
      else do
        -- .casesOn signature: {params...} → {motive} → {idx₁}...{idxₖ} → {w} → (target) → branches...
        let casesOnName := indName ++ `casesOn
        let mut args : Array (Option Expr) := paramsOnly.toArray.map some
        args := args.push (some motive)
        for _ in [:numExtraIndices] do
          args := args.push none         -- extra index (inferred from tExpr)
        args := args.push none           -- w index (inferred from tExpr)
        args := args.push (some tExpr)   -- target
        for lam in branchLams do
          args := args.push (some lam)
        let mut casesResult ← mkAppOptM casesOnName args
        -- Apply rfl for each extra index equality, then for w
        for i in [:numExtraIndices] do
          let rflI ← mkEqRefl extraIdxArgs[i]!
          casesResult := mkApp casesResult rflI
        let rflW ← mkEqRefl wT
        casesResult := mkApp casesResult rflW
        pure casesResult
      -- Handle string associativity cast (shared by both paths)
      let fullStr ← concatStrs cfg ctx start stop
      let mut motiveResultStr := wT
      if tStop < stop then
        let afterStr ← concatStrs cfg ctx tStop stop
        motiveResultStr ← mkAppM ``HAppend.hAppend #[motiveResultStr, afterStr]
      for i in List.range (tStart - start) do
        let idx := tStart - 1 - i
        motiveResultStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, motiveResultStr]
      if ← isDefEq motiveResultStr fullStr then
        return elimResult
      else
        let strEq ← proveStrEq motiveResultStr fullStr
        let goalEq ← mkAppM ``congrArg #[goal, strEq]
        mkAppM ``cast #[goalEq, elimResult]
    else
      throwError "unsupported gterm syntax: {stx}"

-- ═══════════════════════════════════════════════════════════
-- Multi-pattern entry point: [| pat₁ pat₂ ... => body |]
-- ═══════════════════════════════════════════════════════════

/-- Process a single pattern in CPS style, extending the context and alias map,
    then calling the continuation `k` with the updated state. -/
partial def elaborateSinglePatternCPS
    (cfg : ElabConfig)
    (pat : TSyntax `gpat)
    (grammar : Expr) (strExpr : Expr) (parseExpr : Expr)
    (ctx : OrderedCtx) (aliases : AliasMap)
    (k : OrderedCtx → AliasMap → TermElabM Expr)
    : TermElabM Expr :=
  withRef pat do
  match pat with
  -- Bare ident: just push to context
  | `(gpat| $x:ident) => do
    let ov : OrderedVar := ⟨x.getId, grammar, strExpr, parseExpr⟩
    k (ctx.push ov) aliases

  -- Annotated ident: push to context, check type matches
  | `(gpat| ($x:ident : $tyStx)) => do
    let _tyExpr ← Lean.Elab.Term.elabTerm tyStx none
    let ov : OrderedVar := ⟨x.getId, grammar, strExpr, parseExpr⟩
    k (ctx.push ov) aliases

  -- Product pattern: ⟨p₁, p₂⟩ on A & B
  | `(gpat| ⟨$p₁, $p₂⟩) => do
    let (gramA, gramB) ← matchProd cfg grammar
    -- Synthetic name for the ordered-context entry
    let synName := Name.mkSimple s!"_prod{ctx.size}"
    let ov : OrderedVar := ⟨synName, grammar, strExpr, parseExpr⟩
    -- Build projection expressions
    let fstExpr ← mkAppM ``Prod.fst #[parseExpr]
    let sndExpr ← mkAppM ``Prod.snd #[parseExpr]
    -- Extract sub-pattern names (V1: must be bare idents)
    let p₁Name ← match p₁ with
      | `(gpat| $x:ident) => pure x.getId
      | _ => throwError "product sub-patterns must be bare identifiers (nested patterns not yet supported)"
    let p₂Name ← match p₂ with
      | `(gpat| $x:ident) => pure x.getId
      | _ => throwError "product sub-patterns must be bare identifiers (nested patterns not yet supported)"
    let a₁ : Alias := ⟨synName, fstExpr, gramA⟩
    let a₂ : Alias := ⟨synName, sndExpr, gramB⟩
    let newAliases := (aliases.insert p₁Name a₁).insert p₂Name a₂
    k (ctx.push ov) newAliases

  | _ => throwError "unsupported gpat syntax: {pat}"

/-- Elaborate multiple patterns by decomposing right-nested tensors. -/
partial def elaborateMultiPatterns
    (cfg : ElabConfig)
    (pats : Array (TSyntax `gpat))
    (grammar : Expr)
    (strExpr : Expr)
    (parseExpr : Expr)
    (ctx : OrderedCtx)
    (aliases : AliasMap)
    (goal : Expr)
    (body : TSyntax `gterm)
    : TermElabM Expr := do
  if pats.size == 0 then
    throwError "no patterns provided"
  else if pats.size == 1 then
    -- Single pattern: bind it and elaborate body
    elaborateSinglePatternCPS cfg pats[0]! grammar strExpr parseExpr ctx aliases
      fun newCtx newAliases => do
        elaborateOrderedTerm cfg body newCtx 0 newCtx.size goal newAliases
  else
    -- Multiple patterns: decompose grammar as A ⊗ Rest.
    -- Use let-bindings (not elimTensor) so splitting equalities
    -- survive for termination proofs.
    let (gramA, gramRest) ← matchTensor cfg grammar
    let splitExpr ← mkProjection parseExpr `split    -- v.split
    let splitTy ← inferType splitExpr
    withLetDecl `_sp splitTy splitExpr fun spVar => do
      let leftExpr ← mkProjection spVar `left
      let rightExpr ← mkProjection spVar `right
      let fstExpr ← mkProjection parseExpr `fst
      let sndExpr ← mkProjection parseExpr `snd
      withLetDecl `wL cfg.stringTy leftExpr fun wL => do
      withLetDecl `wR cfg.stringTy rightExpr fun wR => do
        let aTy ← whnf (mkApp gramA wL)
        let restTy ← whnf (mkApp gramRest wR)
        withLetDecl `_a aTy fstExpr fun aVar => do
        withLetDecl `_rest restTy sndExpr fun restVar => do
          -- Add splitting equality: wL ++ wR = strExpr
          let eqExpr ← mkProjection spVar `eq
          let eqTy ← inferType eqExpr
          withLetDecl `_h_split eqTy eqExpr fun hSplit => do
            -- Process first pattern, then recurse on remaining patterns
            let firstPat := pats[0]!
            let remainingPats := pats[1:]
            let bodyExpr ← elaborateSinglePatternCPS cfg firstPat gramA wL aVar ctx aliases
              fun newCtx newAliases => do
                elaborateMultiPatterns cfg remainingPats.toArray gramRest wR restVar
                  newCtx newAliases goal body
            -- bodyExpr has type goal(... ++ wL ++ wR)
            -- Need to cast to goal(... ++ strExpr) using the splitting eq
            let wLwR ← mkAppM ``HAppend.hAppend #[wL, wR]
            let needsCast ← do pure (!(← isDefEq wLwR strExpr))
            let castExpr ← if needsCast then do
              -- Build motive for cast: fun s => goal (ctx_prefix ++ s)
              let hasAfter := ctx.size > 0
              let motiveC ← withLocalDecl `s .default cfg.stringTy fun s => do
                let mut fullStr := s
                for i in List.range ctx.size do
                  let idx := ctx.size - 1 - i
                  fullStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, fullStr]
                mkLambdaFVars #[s] (mkApp goal fullStr)
              let eqSymm ← mkAppM ``Eq.symm #[hSplit]
              let congr ← mkAppM ``congrArg #[motiveC, eqSymm]
              mkAppM ``Eq.mpr #[congr, bodyExpr]
            else
              pure bodyExpr
            mkLetFVars #[spVar, wL, wR, aVar, restVar, hSplit] castExpr

elab "[|" pats:gpat+ " => " body:gterm "|]" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let expectedType ← whnf expectedType
  let .forallE _ domTy body₁ _ := expectedType
    | throwError "[| pat => ... |]: expected type ∀ w, A w → B w, got {expectedType}"
  let stringTy := domTy
  let stringTyW ← whnf stringTy
  let alphabetTy ← match stringTyW.getAppFnArgs with
    | (``List, #[α]) => pure α
    | _ => throwError "[| pat => ... |]: expected string type List α, got {stringTy}"
  withLocalDecl `w .default stringTy fun w => do
    let body₁Inst := body₁.instantiate1 w
    let body₁Inst ← whnf body₁Inst
    let .forallE _ aw bw _ := body₁Inst
      | throwError "[| pat => ... |]: expected type ∀ w, A w → B w, got inner {body₁Inst}"
    let awSort ← inferType aw
    let gramLevel := match awSort with
      | .sort (.succ l) => l
      | _ => .zero
    let cfg : ElabConfig := { stringTy, alphabetTy, gramLevel }
    -- Normalize aw/bw to reduce e.g. [] ++ w → w (from ↑g(X ⊸ Y) types).
    -- We target HAppend.hAppend applications only, to avoid unfolding grammar defs.
    let normalizeAppend (e : Expr) : MetaM Expr :=
      Lean.Meta.transform e (pre := fun e => do
        if e.isApp && e.getAppFn.isConstOf ``HAppend.hAppend then
          let e' ← whnf e
          if e' != e then return .done e'
        return .continue)
    let aw ← normalizeAppend aw
    let bw ← normalizeAppend bw
    let gramA ← mkLambdaFVars #[w] aw
    let gramB ← mkLambdaFVars #[w] bw
    withLocalDecl `v .default aw fun v => do
      let bodyExpr ← elaborateMultiPatterns cfg pats gramA w v #[] {} gramB body
      mkLambdaFVars #[w, v] bodyExpr

end LambekD.Elab
