import Lean
import LambekD.Core.Connectives
import LambekD.Elab.Util
import LambekD.Elab.Syntax

/-!
# Grammar inductive types and constructor helpers

The `grammar_inductive` command macro for defining inductive types indexed by strings,
plus constructor resolution and tensor decomposition helpers used by the elaborator.

## New-style constructor syntax

Constructors use `↑(body)` where `body` is a `gcBody`:
- `↑(RetTy)` — zero grammar arguments (empty context)
- `↑(A ⊸ RetTy)` — one grammar argument
- `↑(A ⊸ B ⊸ RetTy)` — two grammar arguments (curried)
- `↑(&[ x ∈ X ] A ⊸ RetTy x)` — with non-linear parameter `x : X`
-/

namespace LambekD

-- ═══════════════════════════════════════════════════════════
-- Tensor flattening helpers (unchanged)
-- ═══════════════════════════════════════════════════════════

/-- Walk right-associated tensor syntax `A ⊗ (B ⊗ (C ⊗ D))` and collect `#[A, B, C, D]`. -/
partial def collectTensorComponents (ty : Lean.Syntax) : Array (Lean.TSyntax `term) :=
  if ty.getKind == `LambekD.«term_⊗_» then
    #[⟨ty[0]⟩] ++ collectTensorComponents ty[2]
  else #[⟨ty⟩]

partial def buildTensorCtorTy (components : Array (Lean.TSyntax `term))
    (prev : Lean.TSyntax `term) (retTy : Lean.TSyntax `term) (idx : Nat)
    : Lean.MacroM (Lean.TSyntax `term) := do
  if components.size == 0 then
    return retTy
  else if components.size == 1 then
    let comp := components[0]!
    `(($comp) $prev → $retTy)
  else
    let sName := Lean.mkIdent (Lean.Name.mkSimple s!"s{idx}")
    let comp := components[0]!
    let rest := components[1:]
    let inner ← buildTensorCtorTy rest.toArray (← `(Splitting.right $sName)) retTy (idx + 1)
    `(∀ ($sName : Splitting $prev), ($comp) (Splitting.left $sName) → $inner)

-- ═══════════════════════════════════════════════════════════
-- ↑(term) syntax for new-style constructor types
-- ═══════════════════════════════════════════════════════════

-- Uses plain `term` inside ↑(...). Since ⊸, &[...], ⊗ are already valid term syntax,
-- we walk the parsed term tree at runtime to extract binders and components.
scoped syntax (name := gcArrow) "↑(" term ")" : term

-- ═══════════════════════════════════════════════════════════
-- Process ↑(term) body to extract binders, components, return type
-- ═══════════════════════════════════════════════════════════

open Lean in
/-- Walk a term syntax tree inside `↑(...)` and extract:
    - `binders`: `&[ x ∈ X ]` indexed product quantifiers (become ∀ in ctor)
    - `components`: grammar arguments before the final `⊸`
    - `retTy`: the return type (last element in the ⊸ chain)

    Recognizes `⊸` (kind `LambekD.«term_⊸_»`) and `&[x ∈ X]` (leading `&[` atom).
    Tensor components `A ⊗ B ⊗ C` are flattened to `[A, B, C]`. -/
partial def processArrowBody (body : Syntax)
    : Array (TSyntax `ident × TSyntax `term) × Array (TSyntax `term) × TSyntax `term :=
  if body.getKind == `LambekD.«term_⊸_» then
    -- A ⊸ rest
    let comp : TSyntax `term := ⟨body[0]⟩
    let rest := body[2]
    let (binders, comps, ret) := processArrowBody rest
    let flatComps := if comp.raw.getKind == `LambekD.«term_⊗_» then
      collectTensorComponents comp.raw
    else #[comp]
    (binders, flatComps ++ comps, ret)
  else if body.getNumArgs ≥ 6 then
    match body[0] with
    | .atom _ "&[" =>
      -- &[x ∈ X] rest — the &[...] term syntax
      let x : TSyntax `ident := ⟨body[1]⟩
      let X : TSyntax `term := ⟨body[3]⟩
      let rest := body[5]
      let (binders, comps, ret) := processArrowBody rest
      (#[(x, X)] ++ binders, comps, ret)
    | _ => (#[], #[], ⟨body⟩)
  else
    -- Base case: return type
    (#[], #[], ⟨body⟩)

-- ═══════════════════════════════════════════════════════════
-- Extract index types from `Q → Bool → Grammar`
-- ═══════════════════════════════════════════════════════════

open Lean in
/-- Check if a syntax node is `Grammar` (bare) or `Grammar X` (applied). -/
private def isGrammarTerminal (ty : Syntax) : Bool :=
  -- Bare `Grammar`
  (ty.isIdent && ty.getId.toString == "Grammar") ||
  -- Application `Grammar X`
  (ty.getKind == ``Lean.Parser.Term.app &&
   ty[0].isIdent && ty[0].getId.toString == "Grammar")

open Lean in
/-- Build the string type syntax from the terminal `Grammar X` of an index type.
    Syntactically replaces `Grammar` with `LambekD.String` in the terminal application.
    For bare `Grammar`, returns `LambekD.String _`.
    For `Grammar X`, returns `LambekD.String X` (preserving the exact syntax of `X`). -/
partial def buildStringTypeFromIdxTy (ty : Syntax) : TSyntax `term :=
  if ty.getKind == ``Lean.Parser.Term.arrow then
    buildStringTypeFromIdxTy ty[2]
  else if ty.getKind == ``Lean.Parser.Term.depArrow then
    buildStringTypeFromIdxTy ty[2]
  else if ty.getKind == ``Lean.Parser.Term.app &&
          ty[0].isIdent && ty[0].getId.toString == "Grammar" then
    -- `Grammar X` → `LambekD.String X`: replace function name, keep argument
    ⟨ty.setArg 0 (mkIdent `LambekD.String)⟩
  else
    -- Bare `Grammar` or fallback → `LambekD.String`
    ⟨mkIdent `LambekD.String⟩

open Lean in
/-- Walk an arrow chain `A → B → ... → Grammar X` and collect domain types.
    Returns `some #[A, B, ...]` if the chain ends with `Grammar` or `Grammar X`,
    `none` otherwise. -/
partial def extractIndexTypes (ty : Syntax) : Option (Array (TSyntax `term)) :=
  -- Check if this is `Grammar` or `Grammar X` (the terminal)
  if isGrammarTerminal ty then
    some #[]
  else
    -- Check if this is an arrow `A → B`
    -- Arrow kind in Lean 4: ``Lean.Parser.Term.arrow``
    if ty.getKind == ``Lean.Parser.Term.arrow then
      let dom : TSyntax `term := ⟨ty[0]⟩
      let cod := ty[2]
      match extractIndexTypes cod with
      | some rest => some (#[dom] ++ rest)
      | none => none
    else
      -- Check for dependent arrow `(x : A) → B`
      if ty.getKind == ``Lean.Parser.Term.depArrow then
        let binder := ty[0] -- bracketedBinder
        -- Extract type from binder
        let dom : TSyntax `term := ⟨binder[1][0]⟩ -- rough extraction
        let cod := ty[2]
        match extractIndexTypes cod with
        | some rest => some (#[dom] ++ rest)
        | none => none
      else
        none

-- ═══════════════════════════════════════════════════════════
-- Old-style grammar_inductive (backward compatible)
-- ═══════════════════════════════════════════════════════════

open Lean Elab Command in
elab "grammar_inductive " name:ident params:bracketedBinder* " where"
    ctors:(ppLine "| " ident " : " term)* : command => do
  let w := mkIdent `w
  -- Use a hole `_` for the alphabet since old-style doesn't specify it explicitly
  let alphHole : TSyntax `term :=
    ⟨Syntax.node SourceInfo.none ``Lean.Parser.Term.hole #[Syntax.atom SourceInfo.none "_"]⟩
  -- Build return type: name p₁ ... pₙ w
  let mut retTy : TSyntax `term ← `($name)
  for param in params do
    for id in param.raw[1].getArgs do
      let idStx : TSyntax `ident := ⟨id⟩
      retTy ← `($retTy $idStx)
  retTy ← `($retTy $w)
  -- Build base command with w as index: `inductive Name params : LambekD.String _ → Type _ where`
  let baseCmd ← `(inductive $name $[$params]* : LambekD.String $alphHole → Type _ where)
  let emptyDeclMods := Syntax.node SourceInfo.none
    ``Lean.Parser.Command.declModifiers
    #[.node .none `null #[], .node .none `null #[], .node .none `null #[],
      .node .none `null #[], .node .none `null #[], .node .none `null #[]]
  let mut ctorNodes : Array Syntax := #[]
  for ctor in ctors do
    let c := ctor.raw[1]
    let ty : TSyntax `term := ⟨ctor.raw[3]⟩
    let ctorTy ← if ty.raw.getKind == `LambekD.«term_⊗_» then do
      let components := collectTensorComponents ty.raw
      let inner ← liftMacroM <| buildTensorCtorTy components w retTy 0
      `(∀ ($w : LambekD.String $alphHole), $inner)
    else
      `(∀ ($w : LambekD.String $alphHole), ($ty) $w → $retTy)
    let typeSpec := Syntax.node SourceInfo.none ``Lean.Parser.Term.typeSpec
      #[.atom .none ":", ctorTy.raw]
    let optSig := Syntax.node SourceInfo.none ``Lean.Parser.Command.optDeclSig
      #[.node .none `null #[],
        .node .none `null #[typeSpec]]
    ctorNodes := ctorNodes.push <|
      Syntax.node SourceInfo.none ``Lean.Parser.Command.ctor
        #[.node .none `null #[], .atom .none "|", emptyDeclMods, c, optSig]
  let cmdRaw := baseCmd.raw
  let indNode := cmdRaw[1]
  let indNode' := indNode.setArg 4 (.node .none `null ctorNodes)
  let cmdRaw' := cmdRaw.setArg 1 indNode'
  elabCommand ((⟨cmdRaw'⟩ : TSyntax `command))

-- ═══════════════════════════════════════════════════════════
-- New-style grammar_inductive with ↑(gcBody) and optional indices
-- ═══════════════════════════════════════════════════════════

open Lean Elab Command in
elab "grammar_inductive " name:ident params:bracketedBinder*
    " : " idxTy:term " where"
    ctors:(ppLine "| " ident " : " term)* : command => do
  let w := mkIdent `w
  -- Extract index types from `Q → Bool → ... → Grammar X`
  let some indexTypes := extractIndexTypes idxTy
    | throwError "grammar_inductive: index type must end with `→ Grammar` or `→ Grammar X`, got: {idxTy}"
  -- Build string type by replacing Grammar with LambekD.String in the terminal
  let stringTy := buildStringTypeFromIdxTy idxTy
  -- Build inductive type sig: Name params : Idx₁ → ... → LambekD.String X → Type _
  let mut sigTy : TSyntax `term ← `(Type _)
  sigTy ← `($stringTy → $sigTy)
  for idx in indexTypes.reverse do
    sigTy ← `($idx → $sigTy)
  let baseCmd ← `(inductive $name $[$params]* : $sigTy where)
  let emptyDeclMods := Syntax.node SourceInfo.none
    ``Lean.Parser.Command.declModifiers
    #[.node .none `null #[], .node .none `null #[], .node .none `null #[],
      .node .none `null #[], .node .none `null #[], .node .none `null #[]]
  let mut ctorNodes : Array Syntax := #[]
  for ctor in ctors do
    let c := ctor.raw[1]
    let ty : TSyntax `term := ⟨ctor.raw[3]⟩
    let ctorTy ← if ty.raw.getKind == `LambekD.gcArrow then
      -- New-style: ↑(term) — extract the term from child [1]
      let body := ty.raw[1]
      let (binders, components, retTyRaw) := processArrowBody body
      let retTy : TSyntax `term ← `($retTyRaw $w)
      let ctorTyInner ← if components.size == 0 then
        `(ε $w → $retTy)
      else if components.size == 1 then
        let comp := components[0]!
        `(($comp) $w → $retTy)
      else
        liftMacroM <| buildTensorCtorTy components w retTy 0
      let mut ct : TSyntax `term ← `(∀ ($w : $stringTy), $ctorTyInner)
      for (x, X) in binders.reverse do
        ct ← `(∀ ($x : $X), $ct)
      pure ct
    else if ty.raw.getKind == `LambekD.«term_⊗_» then
      -- Old-style tensor: A ⊗ B ⊗ C → flatten
      -- Build return type: name p₁ ... pₙ w
      let mut retTy : TSyntax `term ← `($name)
      for param in params do
        for id in param.raw[1].getArgs do
          let idStx : TSyntax `ident := ⟨id⟩
          retTy ← `($retTy $idStx)
      retTy ← `($retTy $w)
      let components := collectTensorComponents ty.raw
      let inner ← liftMacroM <| buildTensorCtorTy components w retTy 0
      `(∀ ($w : $stringTy), $inner)
    else
      -- Old-style simple: A w → RetTy w
      let mut retTy : TSyntax `term ← `($name)
      for param in params do
        for id in param.raw[1].getArgs do
          let idStx : TSyntax `ident := ⟨id⟩
          retTy ← `($retTy $idStx)
      retTy ← `($retTy $w)
      `(∀ ($w : $stringTy), ($ty) $w → $retTy)
    let typeSpec := Syntax.node SourceInfo.none ``Lean.Parser.Term.typeSpec
      #[.atom .none ":", ctorTy.raw]
    let optSig := Syntax.node SourceInfo.none ``Lean.Parser.Command.optDeclSig
      #[.node .none `null #[],
        .node .none `null #[typeSpec]]
    ctorNodes := ctorNodes.push <|
      Syntax.node SourceInfo.none ``Lean.Parser.Command.ctor
        #[.node .none `null #[], .atom .none "|", emptyDeclMods, c, optSig]
  -- Splice ctors into the inductive command
  let cmdRaw := baseCmd.raw
  let indNode := cmdRaw[1]
  let indNode' := indNode.setArg 4 (.node .none `null ctorNodes)
  let cmdRaw' := cmdRaw.setArg 1 indNode'
  elabCommand ((⟨cmdRaw'⟩ : TSyntax `command))

end LambekD

-- ═══════════════════════════════════════════════════════════
-- Elaborator helpers (unchanged)
-- ═══════════════════════════════════════════════════════════

namespace LambekD.Elab

open Lean Elab Term Meta
open LambekD

def getInductiveVal (env : Lean.Environment) (name : Lean.Name) : Option Lean.InductiveVal :=
  match env.find? name with
  | some (.inductInfo v) => some v
  | _ => none

/-- Resolve the fully qualified constructor name for a grammar_inductive -/
def resolveCtorName (cfg : ElabConfig) (goal : Expr) (ctorName : Name)
    : TermElabM Name := do
  withLocalDecl `w .default cfg.stringTy fun w => do
    let goalW ← whnf (mkApp goal w)
    let indName := goalW.getAppFn.constName!
    let fullCtorName := indName ++ ctorName
    let env ← getEnv
    let some _ := env.find? fullCtorName
      | throwError "constructor '{fullCtorName}' not found"
    return fullCtorName

/-- Like `resolveCtorName` but returns `Option Name` instead of throwing. -/
def tryResolveCtorName (cfg : ElabConfig) (goal : Expr) (ctorName : Name)
    : TermElabM (Option Name) := do
  try
    let name ← resolveCtorName cfg goal ctorName
    return some name
  catch _ =>
    return none

/-- Instantiate a ctor with the inductive's universe levels and parameters.
    Returns (ctorTypeAfterParams, ctorConst, params) or `none`. -/
def instantiateCtorFull (cfg : ElabConfig) (goal : Expr) (fullCtorName : Name)
    : TermElabM (Option (Expr × Expr × Array Expr)) := do
  withLocalDecl `w .default cfg.stringTy fun w => do
    let goalW ← whnf (mkApp goal w)
    let indName := goalW.getAppFn.constName!
    let env ← getEnv
    let some ci := env.find? fullCtorName | return none
    let some indVal := getInductiveVal env indName | return none
    let numParams := indVal.numParams
    let args := goalW.getAppArgs
    let paramsOnly := args[:numParams]
    let indLevels := goalW.getAppFn.constLevels!
    -- Map ctor level params to concrete levels from goal
    let ctorLevels := ci.levelParams.map fun lp =>
      match indLevels.zip indVal.levelParams |>.find? (·.2 == lp) with
      | some (l, _) => l
      | none => .zero
    let ctorConst := Lean.mkConst fullCtorName ctorLevels
    let ctorInst := ci.type.instantiateLevelParams ci.levelParams ctorLevels
    let mut ty := ctorInst
    for p in paramsOnly do
      match ty with
      | .forallE _ _ body _ => ty := body.instantiate1 p
      | _ => return none
    return some (ty, ctorConst, paramsOnly.toArray)

/-- Skip non-linear `∀` binders (from `&[x ∈ X]`) before the `w : String` binder.
    Returns (count of non-linear binders, type starting from `∀ (w : String), ...`). -/
def skipNonLinearBinders (cfg : ElabConfig) (ctyAfterParams : Expr)
    : TermElabM (Nat × Expr) := do
  let mut ty := ctyAfterParams
  let mut count := 0
  repeat
    match ty with
    | .forallE _ dom body _ =>
      if ← isDefEq (← whnf dom) cfg.stringTy then break
      count := count + 1
      let mv ← mkFreshExprMVar (some dom)
      ty := body.instantiate1 mv
    | _ => break
  return (count, ty)

/-- Count consecutive non-linear `∀` binders before `w : String` in a ctor type (after params). -/
def countNonLinearBinders (cfg : ElabConfig) (ctyAfterParams : Expr) : TermElabM Nat := do
  let (count, _) ← skipNonLinearBinders cfg ctyAfterParams
  return count

/-- Check if a ctor is a zero-component ctor (arg type is Epsilon after non-linear binders + w).
    Zero-component ctors arise from `↑(&[...] RetTy)` with no `⊸`. -/
def isZeroComponentCtor (cfg : ElabConfig) (ctyAfterParams : Expr) : TermElabM Bool := do
  let (_, ty) ← skipNonLinearBinders cfg ctyAfterParams
  match ty with
  | .forallE _ _ afterW _ =>
    withLocalDecl `ww .default cfg.stringTy fun ww => do
      let body := afterW.instantiate1 ww
      match body with
      | .forallE _ argTy _ _ =>
        -- Check if arg type head is Epsilon (use withReducible to avoid unfolding the def)
        let argTyH ← withReducible <| whnf argTy
        return argTyH.isAppOf ``Epsilon
      | _ => return false
  | _ => return false

/-- Convert simple gterm syntax to term syntax for non-linear arg elaboration.
    Handles idents, nums, `#(term)`, parenthesized, and application forms. -/
partial def gtermToTermSyntax (stx : TSyntax `gterm) : TermElabM (TSyntax `term) := do
  match stx with
  | `(gterm| $x:ident) => `($x)
  | `(gterm| $n:num) => `($n)
  | `(gterm| #($t:term)) => return t
  | `(gterm| ($inner)) => do
    let t ← gtermToTermSyntax inner
    `(($t))
  | `(gterm| $f $a) => do
    let tf ← gtermToTermSyntax f
    let ta ← gtermToTermSyntax a
    `($tf $ta)
  | _ => throwError "cannot convert gterm to term syntax: {stx}\nUse #(term) to embed arbitrary Lean terms"

/-- Count the number of Splitting binders in a ctor type after the `w` parameter.
    Skips non-linear binders before `w`. Returns 0 if not tensor-flattened. -/
def countTensorSplittings (cfg : ElabConfig) (goal : Expr) (fullCtorName : Name)
    : TermElabM Nat := do
  let some (ty, _, _) ← instantiateCtorFull cfg goal fullCtorName | return 0
  -- Skip non-linear binders before w : String
  let (_, cty) ← skipNonLinearBinders cfg ty
  withLocalDecl `w .default cfg.stringTy fun w => do
    -- cty: ∀ (w : String), ... → RetTy w
    match cty with
    | .forallE _ _ afterW _ =>
      let mut body := afterW.instantiate1 w
      let mut count := 0
      -- Count consecutive Splitting binders (each followed by a component)
      while true do
        match body with
        | .forallE _ splitTy afterS _ =>
          let splitTyW ← whnf splitTy
          if splitTyW.getAppFn.isConstOf ``Splitting then
            count := count + 1
            -- Skip the splitting binder and the left-component binder
            let sVar ← mkFreshExprMVar (some splitTyW)
            let afterSInst := afterS.instantiate1 sVar
            match afterSInst with
            | .forallE _ _ rest _ =>
              let dummy ← mkFreshExprMVar none
              body := rest.instantiate1 dummy
            | _ => break
          else
            break
        | _ => break
      return count
    | _ => return 0

/-- Check if a constructor is tensor-flattened. -/
def isTensorCtor (cfg : ElabConfig) (goal : Expr) (fullCtorName : Name)
    : TermElabM Bool := do
  let n ← countTensorSplittings cfg goal fullCtorName
  return n > 0

/-- Recursively decompose a tensor value to produce ctor args for a multi-tensor flattened ctor.
    `body` is the ctor type after params + w. For each Splitting binder, extracts `.split`, `.fst`,
    and recurses into `.snd`. Returns the array of args to pass to the ctor. -/
partial def decomposeTensorForCtor (tExpr : Expr) (body : Expr) : TermElabM (Array Expr) := do
  match body with
  | .forallE _ splitTy afterS _ =>
    let splitTyW ← whnf splitTy
    if splitTyW.getAppFn.isConstOf ``Splitting then
      let splitE ← mkAppM ``Tensor.split #[tExpr]
      let fstE ← mkAppM ``Tensor.fst #[tExpr]
      let sVar ← mkFreshExprMVar (some splitTyW)
      let afterSInst := afterS.instantiate1 sVar
      match afterSInst with
      | .forallE _ _ rest _ =>
        let dummy ← mkFreshExprMVar none
        let restBody := rest.instantiate1 dummy
        match restBody with
        | .forallE _ nextSplitTy _ _ =>
          let nextSplitTyW ← whnf nextSplitTy
          if nextSplitTyW.getAppFn.isConstOf ``Splitting then
            let sndE ← mkAppM ``Tensor.snd #[tExpr]
            let innerArgs ← decomposeTensorForCtor sndE restBody
            return #[splitE, fstE] ++ innerArgs
          else
            let sndE ← mkAppM ``Tensor.snd #[tExpr]
            return #[splitE, fstE, sndE]
        | _ =>
          let sndE ← mkAppM ``Tensor.snd #[tExpr]
          return #[splitE, fstE, sndE]
      | _ => throwError "unexpected tensor ctor shape in decomposeTensorForCtor"
    else
      return #[tExpr]
  | _ => return #[tExpr]

/-- CPS helper for rec branches of tensor-flattened constructors. -/
partial def withTensorCtorBinders (cfg : ElabConfig) (body : Expr)
    (k : Array Expr → Expr → Expr → TermElabM Expr) : TermElabM Expr := do
  match body with
  | .forallE _ splitTy afterS _ =>
    let splitTyW ← whnf splitTy
    if !splitTyW.getAppFn.isConstOf ``Splitting then
      throwError "withTensorCtorBinders: expected Splitting, got {← ppExpr splitTyW}"
    withLocalDecl `s .default splitTy fun sVar => do
      let sLeft ← mkAppM ``Splitting.left #[sVar]
      let sRight ← mkAppM ``Splitting.right #[sVar]
      let afterSInst := afterS.instantiate1 sVar
      match afterSInst with
      | .forallE _ leftTy rest _ =>
        withLocalDecl `a .default leftTy fun aVar => do
          let leftGram ← withLocalDecl `ww .default cfg.stringTy fun ww => do
            abstractGrammarReplace ww leftTy sLeft
          let restInst := rest.instantiate1 aVar
          match restInst with
          | .forallE _ nextSplitTy _ _ =>
            let nextSplitTyW ← whnf nextSplitTy
            if nextSplitTyW.getAppFn.isConstOf ``Splitting then
              withTensorCtorBinders cfg restInst fun innerFvars innerVal innerGram => do
                let tensorVal ← mkAppM ``Tensor.mk #[sVar, aVar, innerVal]
                let tensorGram ← mkAppM ``Tensor #[leftGram, innerGram]
                k (#[sVar, aVar] ++ innerFvars) tensorVal tensorGram
            else
              withLocalDecl `b .default nextSplitTy fun bVar => do
                let rightGram ← withLocalDecl `ww .default cfg.stringTy fun ww => do
                  abstractGrammarReplace ww nextSplitTy sRight
                let tensorVal ← mkAppM ``Tensor.mk #[sVar, aVar, bVar]
                let tensorGram ← mkAppM ``Tensor #[leftGram, rightGram]
                k #[sVar, aVar, bVar] tensorVal tensorGram
          | _ =>
            throwError "withTensorCtorBinders: unexpected shape after component"
      | _ => throwError "withTensorCtorBinders: expected component after Splitting"
  | _ => throwError "withTensorCtorBinders: expected forallE with Splitting"

/-- CPS helper for multi-arity rec patterns. -/
partial def withTensorCtorComponents (cfg : ElabConfig) (body : Expr)
    (k : Array Expr → Array (Expr × Expr × Expr) → TermElabM Expr) : TermElabM Expr := do
  match body with
  | .forallE _ splitTy afterS _ =>
    let splitTyW ← whnf splitTy
    if !splitTyW.getAppFn.isConstOf ``Splitting then
      throwError "withTensorCtorComponents: expected Splitting, got {← ppExpr splitTyW}"
    withLocalDecl `s .default splitTy fun sVar => do
      let sLeft ← mkAppM ``Splitting.left #[sVar]
      let sRight ← mkAppM ``Splitting.right #[sVar]
      let afterSInst := afterS.instantiate1 sVar
      match afterSInst with
      | .forallE _ leftTy rest _ =>
        withLocalDecl `a .default leftTy fun aVar => do
          let leftGram ← withLocalDecl `ww .default cfg.stringTy fun ww => do
            abstractGrammarReplace ww leftTy sLeft
          let restInst := rest.instantiate1 aVar
          let comp := (leftGram, sLeft, aVar)
          match restInst with
          | .forallE _ nextSplitTy _ _ =>
            let nextSplitTyW ← whnf nextSplitTy
            if nextSplitTyW.getAppFn.isConstOf ``Splitting then
              withTensorCtorComponents cfg restInst fun innerFvars innerComps => do
                k (#[sVar, aVar] ++ innerFvars) (#[comp] ++ innerComps)
            else
              withLocalDecl `b .default nextSplitTy fun bVar => do
                let rightGram ← withLocalDecl `ww .default cfg.stringTy fun ww => do
                  abstractGrammarReplace ww nextSplitTy sRight
                let lastComp := (rightGram, sRight, bVar)
                k #[sVar, aVar, bVar] #[comp, lastComp]
          | _ =>
            throwError "withTensorCtorComponents: unexpected shape after component"
      | _ => throwError "withTensorCtorComponents: expected component after Splitting"
  | _ => throwError "withTensorCtorComponents: expected forallE with Splitting"

/-- Check if a component grammar references the given inductive type (i.e., is a recursive field). -/
def isRecursiveComponent (cfg : ElabConfig) (indName : Name) (gram : Expr) : TermElabM Bool := do
  withLocalDecl `_w .default cfg.stringTy fun w => do
    let ty ← whnf (mkApp gram w)
    return ty.getAppFn.isConstOf indName

/-- Information about a non-linear binder position in a case branch.
    Either a bare ident (just a name) or a pattern (with variables and match info). -/
inductive NLBinderInfo where
  | ident (name : Name)
  | pattern (freshName : Name) (patternStx : Syntax)
deriving Inhabited

/-- Parse a gbranchVar syntax node: returns `NLBinderInfo`.
    For bare idents: `.ident name`. For `(term)`: `.pattern freshName termStx`. -/
def parseGBranchVar (stx : Syntax) (idx : Nat) : NLBinderInfo :=
  -- Direct ident (e.g., from old-style syntax)
  if stx.isIdent then
    .ident stx.getId
  -- gbranchVar wrapping a bare ident: 1 child which is the ident
  else if stx.getNumArgs == 1 && stx[0].isIdent then
    .ident stx[0].getId
  -- `( term )` form: 3 children = "(", term, ")"
  else if stx.getNumArgs >= 3 then
    .pattern (Name.mkSimple s!"_nlpat_{idx}") stx[1]
  else
    .ident (Name.mkSimple s!"_nl_{idx}")

/-- Build a casesOn wrapper for a non-linear binder pattern match.
    Given `nlFvar : InductiveTy`, pattern var fvars, the matching constructor index,
    and a body expression that references the pattern vars, builds:
    `InductiveTy.casesOn nlFvar <sorry>... (fun patVars => body) ...<sorry>` -/
def wrapWithNLMatch (nlFvar : Expr) (patVarFvars : Array Expr)
    (ctorIdx : Nat) (bodyExpr : Expr) : TermElabM Expr := do
  let nlTy ← whnf (← inferType nlFvar)
  let indName := nlTy.getAppFn.constName!
  let env ← getEnv
  let some indVal := getInductiveVal env indName
    | throwError "not an inductive: {indName}"
  let indArgs := nlTy.getAppArgs
  let indParams := indArgs[:indVal.numParams]
  let indLevels := nlTy.getAppFn.constLevels!
  let bodyTy ← inferType bodyExpr
  -- Build motive: fun (x : nlTy) => bodyTy (constant motive, body type doesn't depend on x)
  let motive ← withLocalDecl `_x .default nlTy fun x =>
    mkLambdaFVars #[x] bodyTy
  -- Build casesOn args
  let casesOnName := indName ++ `casesOn
  -- casesOn signature: {params...} → {motive} → (target) → branches...
  let mut args : Array (Option Expr) := #[]
  for p in indParams do
    args := args.push (some p)
  args := args.push (some motive)
  args := args.push (some nlFvar)  -- discriminant
  -- Build arms
  for (ctorName, i) in indVal.ctors.zipIdx.toArray do
    if i == ctorIdx then
      -- Matching arm: abstract pattern vars from body
      let arm ← mkLambdaFVars patVarFvars bodyExpr
      args := args.push (some arm)
    else
      -- Non-matching arm: build lambda with the right arity, body is sorry
      let some ci := env.find? ctorName | throwError "ctor not found: {ctorName}"
      let ctorTy := ci.type.instantiateLevelParams ci.levelParams indLevels
      let mut ty := ctorTy
      for p in indParams do
        match ty with
        | .forallE _ _ b _ => ty := b.instantiate1 p
        | _ => throwError "unexpected ctor shape in wrapWithNLMatch"
      -- ty: ∀ (args...) → IndTy ...
      -- Build: fun args => sorry
      let mut fvars : Array Expr := #[]
      let mut curTy := ty
      for _ in [:100] do
        match curTy with
        | .forallE n d b bi =>
          let fvar ← withLocalDecl n bi d fun fv => pure fv
          fvars := fvars.push fvar
          curTy := b.instantiate1 fvar
        | _ => break
      -- Actually we need to use withLocalDecl in CPS... let me use forallBoundedTelescope
      let arm ← forallBoundedTelescope ty none fun fvs _ => do
        let sorryExpr ← mkSorry bodyTy (synthetic := true)
        mkLambdaFVars fvs sorryExpr
      args := args.push (some arm)
  mkAppOptM casesOnName args

/-- Build a casesOn wrapper with ALL arms filled in (for multi-branch NL pattern matching).
    `arms[i]` is a pre-abstracted lambda for constructor `i`'s casesOn branch. -/
def wrapWithNLMatchAll (nlFvar : Expr) (bodyTy : Expr)
    (arms : Array Expr)
    : TermElabM Expr := do
  let nlTy ← whnf (← inferType nlFvar)
  let indName := nlTy.getAppFn.constName!
  let env ← getEnv
  let some indVal := getInductiveVal env indName
    | throwError "not an inductive: {indName}"
  let indArgs := nlTy.getAppArgs
  let indParams := indArgs[:indVal.numParams]
  -- Build motive: fun (x : nlTy) => bodyTy (constant motive)
  let motive ← withLocalDecl `_x .default nlTy fun x =>
    mkLambdaFVars #[x] bodyTy
  let casesOnName := indName ++ `casesOn
  let mut args : Array (Option Expr) := #[]
  for p in indParams do
    args := args.push (some p)
  args := args.push (some motive)
  args := args.push (some nlFvar)
  for arm in arms do
    args := args.push (some arm)
  mkAppOptM casesOnName args

end LambekD.Elab
