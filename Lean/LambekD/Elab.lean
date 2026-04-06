import Lean

namespace LambekD

universe uAlph uGram
class AlphabetStr where
  Alphabet : Type uAlph
  instInahbited : Inhabited Alphabet
  instDecEq : DecidableEq Alphabet

open AlphabetStr

variable [AlphabetStr]

abbrev String := List Alphabet

abbrev Grammar := String → Type uGram

structure Splitting (w : String) where
  left : String
  right : String
  eq : left ++ right = w

@[reducible] def splitting (l r : String) : Splitting (l ++ r) := ⟨l, r, rfl⟩

structure Tensor (A B : Grammar) (w : String) where
  split : Splitting w
  fst : A split.left
  snd : B split.right

def Epsilon : Grammar := fun w => ULift.{uGram} (PLift (w = []))
def Literal (c : Alphabet) : Grammar := fun w => ULift.{uGram} (PLift (w = [c]))
def FunctionR (A B : Grammar) : Grammar := fun w => ∀ w', A w' → B (w' ++ w)
def FunctionL (B A : Grammar) : Grammar := fun w => ∀ w', A w' → B (w ++ w')
def Sum (A B : Grammar) : Grammar := fun w => A w ⊕ B w
def Product (A B : Grammar) : Grammar := fun w => A w × B w
def Top : Grammar := fun _ => ULift.{uGram} PUnit
def Bottom : Grammar := fun _ => ULift.{uGram} PEmpty
def IdxProduct.{v} (X : Type v) (F : X → Grammar) : Grammar := fun w => ∀ x, F x w
def IdxCoproduct.{v} (X : Type v) (F : X → Grammar) : Grammar := fun w => Σ x, F x w

def GrammarTerm (A B : Grammar) := ∀ w, A w → B w

scoped infixr:70 " ⊗ "  => Tensor
scoped infixr:60 " ⊸ "  => FunctionR
scoped infixl:60 " ⟜ "  => FunctionL
scoped infixl:65 " ⊕ "  => Sum
scoped infixl:70 " & "  => Product
scoped infixl:25 " ⊢ "  => GrammarTerm
scoped notation "⊤g" => Top
scoped notation "⊥g" => Bottom
scoped notation "lit(" c ")" => Literal c
scoped notation "ε" => Epsilon
scoped syntax:50 "&[" ident " ∈ " term "]" term:50 : term
scoped syntax:50 "⊕[" ident " ∈ " term "]" term:50 : term

scoped macro_rules
  | `(&[$x:ident ∈ $X] $F) => `(IdxProduct $X (fun $x => $F))
scoped macro_rules
  | `(⊕[$x:ident ∈ $X] $F) => `(IdxCoproduct $X (fun $x => $F))

def elimTensor {A B : Grammar} (C : String → Sort _) {w : String}
    (t : Tensor A B w) (body : (wL wR : String) → A wL → B wR → C (wL ++ wR))
    : C w := t.split.eq ▸ body t.split.left t.split.right t.fst t.snd

def elimEpsilon (C : String → Sort _) {w : String}
    (t : Epsilon w) (body : C []) : C w := t.down.down ▸ body

-- grammar_inductive: builds an inductive with `w : String` as an index (not parameter).
-- Using an index allows recursive occurrences to be partially applied (e.g., `StarG A`
-- inside `A ⊗ StarG A`), which is required for grammar-level recursive types.
-- Tensor (⊗) in ctor types is flattened to avoid Lean's nested inductive restrictions.

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

open Lean Elab Command in
elab "grammar_inductive " name:ident params:bracketedBinder* " where"
    ctors:(ppLine "| " ident " : " term)* : command => do
  let w := mkIdent `w
  -- Build return type: name p₁ ... pₙ w
  let mut retTy : TSyntax `term ← `($name)
  for param in params do
    for id in param.raw[1].getArgs do
      let idStx : TSyntax `ident := ⟨id⟩
      retTy ← `($retTy $idStx)
  retTy ← `($retTy $w)
  -- Build base command with w as index: `inductive Name params : LambekD.String → Type _ where`
  let baseCmd ← `(inductive $name $[$params]* : LambekD.String → Type _ where)
  -- Build ctor nodes by hand (ctor quotation not available here)
  -- Lean's ctor parser produces 5 children:
  --   [0] null node (leading whitespace group)
  --   [1] atom "|"
  --   [2] declModifiers (6 empty null children)
  --   [3] ident (ctor name)
  --   [4] optDeclSig (with Term.typeSpec wrapping ":" + type)
  let emptyDeclMods := Syntax.node SourceInfo.none
    ``Lean.Parser.Command.declModifiers
    #[.node .none `null #[], .node .none `null #[], .node .none `null #[],
      .node .none `null #[], .node .none `null #[], .node .none `null #[]]
  let mut ctorNodes : Array Syntax := #[]
  for ctor in ctors do
    let c := ctor.raw[1]
    let ty : TSyntax `term := ⟨ctor.raw[3]⟩
    -- Detect tensor: if ty has kind `LambekD.«term_⊗_»`, flatten to avoid nested inductive
    -- A ⊗ B ⊗ C → ∀ (w : String) (s0 : Splitting w), A s0.left → ∀ (s1 : Splitting s0.right), B s1.left → C s1.right → RetTy
    let ctorTy ← if ty.raw.getKind == `LambekD.«term_⊗_» then do
      let components := collectTensorComponents ty.raw
      let inner ← liftMacroM <| buildTensorCtorTy components w retTy 0
      `(∀ ($w : LambekD.String), $inner)
    else
      `(∀ ($w : LambekD.String), ($ty) $w → $retTy)
    let typeSpec := Syntax.node SourceInfo.none ``Lean.Parser.Term.typeSpec
      #[.atom .none ":", ctorTy.raw]
    let optSig := Syntax.node SourceInfo.none ``Lean.Parser.Command.optDeclSig
      #[.node .none `null #[],
        .node .none `null #[typeSpec]]
    ctorNodes := ctorNodes.push <|
      Syntax.node SourceInfo.none ``Lean.Parser.Command.ctor
        #[.node .none `null #[], .atom .none "|", emptyDeclMods, c, optSig]
  -- Splice ctors into the inductive command: declaration[1] = inductive, inductive[4] = ctors
  let cmdRaw := baseCmd.raw
  let indNode := cmdRaw[1]
  let indNode' := indNode.setArg 4 (.node .none `null ctorNodes)
  let cmdRaw' := cmdRaw.setArg 1 indNode'
  elabCommand ((⟨cmdRaw'⟩ : TSyntax `command))

end LambekD

namespace LambekD.Elab

open Lean Elab Term Meta
open LambekD

structure OrderedVar where
  userName : Name
  grammar  : Expr
  strExpr  : Expr
  parseExpr : Expr
deriving Inhabited

abbrev OrderedCtx := Array OrderedVar

def OrderedCtx.getV (ctx : OrderedCtx) (i : Nat) : OrderedVar :=
  if h : i < ctx.size then ctx[i] else default

-- Alias: maps a user-facing name (e.g., `a` from ⟨a, b⟩) to an ordered-context
-- variable with a projection expression
structure Alias where
  ctxName : Name        -- synthetic ordered-context variable name (e.g., `_prod0`)
  projExpr : Expr       -- projection expression (Prod.fst v or Prod.snd v)
  projGrammar : Expr    -- grammar of the projection (A or B)

abbrev AliasMap := Std.HashMap Name Alias

def resolveAliases (aliases : AliasMap) (names : Lean.NameSet) : Lean.NameSet :=
  names.fold (init := {}) fun acc n =>
    match aliases.get? n with
    | some a => acc.insert a.ctxName
    | none   => acc.insert n

structure ElabConfig where
  stringTy : Expr      -- The string type (e.g., `List Paren`)
  alphabetTy : Expr    -- The alphabet type (e.g., `Paren`)
  gramLevel : Level     -- The universe level of Grammar (e.g., `0`)

declare_syntax_cat gterm

syntax ident : gterm
syntax "ε" : gterm
syntax "tt" : gterm
syntax "(" gterm ", " gterm ")" : gterm
syntax "let" "(" ident ", " ident ")" "=" gterm "in" gterm : gterm
syntax "let" "⟨⟩" "=" gterm "in" gterm : gterm
syntax "let" "(" ")" "=" gterm "in" gterm : gterm
syntax "fun" "(" ident ":" term ")" "=>" gterm : gterm
syntax "funL" "(" ident ":" term ")" "=>" gterm : gterm
syntax:10 gterm:10 gterm:11 : gterm
syntax "⟨" gterm ", " gterm "⟩" : gterm
syntax "fst" gterm:11 : gterm
syntax "snd" gterm:11 : gterm
syntax "inl" gterm:11 : gterm
syntax "inr" gterm:11 : gterm
syntax "case" gterm "of" "|" "inl" ident "=>" gterm
                         "|" "inr" ident "=>" gterm : gterm
syntax "absurd" gterm : gterm
syntax "#[" term "]" gterm:11 : gterm
syntax "Λ" "(" ident ":" term ")" "=>" gterm : gterm
syntax gterm:10 "⌈" term "⌉" : gterm
syntax "σ⟨" term ", " gterm "⟩" : gterm
syntax "caseDep" gterm "of" "|" "σ⟨" ident ", " ident "⟩" "=>" gterm : gterm
syntax "fold" ident gterm:11 : gterm
syntax (name := recGterm) "rec" gterm "of" ("|" ident ident+ "=>" gterm)* : gterm
syntax "sorry" : gterm
syntax "(" gterm ")" : gterm

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
    (aliases : AliasMap := {})
    : TermElabM Nat := do
  let leftNames  := resolveAliases aliases (collectAllIdents leftStx)
  let rightNames := resolveAliases aliases (collectAllIdents rightStx)
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
private def etaReduceGrammar (goal : Expr) : MetaM Expr := do
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

/-- Format the linear context for IDE display.
    Shows linear variables with eta-reduced grammar types.
    Synthetic variables (backing product patterns) are hidden;
    their user-facing aliases are shown instead. -/
private def formatLinearCtx (ctx : OrderedCtx) (start stop : Nat)
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
private def registerLinearCtxInfo (stx : Syntax) (ctx : OrderedCtx) (start stop : Nat)
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

def matchTensor (cfg : ElabConfig) (goal : Expr) : TermElabM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``Tensor, #[_, a, b]) => return (a, b)
  | _ =>
    -- Handle metavar goals by unifying with Tensor ?A ?B
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy)
    let mB ← mkFreshExprMVar (some gramTy)
    let tGoal ← mkAppM ``Tensor #[mA, mB]
    if ← isDefEq goal tGoal then
      return (← instantiateMVars mA, ← instantiateMVars mB)
    else
      throwError "expected A ⊗ B (Tensor), got {← ppExpr goal}"

def matchLinFunR (goal : Expr) : MetaM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``FunctionR, #[_, a, b]) => return (a, b)
  | _ => throwError "expected A ⊸ B (LinFunR), got {← ppExpr goal}"

def matchLinFunL (goal : Expr) : MetaM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``FunctionL, #[_, b, a]) => return (b, a)
  | _ => throwError "expected B ⟜ A (LinFunL), got {← ppExpr goal}"

def matchSum (cfg : ElabConfig) (goal : Expr) : TermElabM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``Sum, #[_, a, b]) => return (a, b)
  | _ =>
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy)
    let mB ← mkFreshExprMVar (some gramTy)
    let sGoal ← mkAppM ``Sum #[mA, mB]
    if ← isDefEq goal sGoal then
      return (← instantiateMVars mA, ← instantiateMVars mB)
    else
      throwError "expected A ⊕ B (Sum), got {← ppExpr goal}"

def matchProd (cfg : ElabConfig) (goal : Expr) : TermElabM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``Product, #[_, a, b]) => return (a, b)
  | _ =>
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy)
    let mB ← mkFreshExprMVar (some gramTy)
    let pGoal ← mkAppM ``Product #[mA, mB]
    if ← isDefEq goal pGoal then
      return (← instantiateMVars mA, ← instantiateMVars mB)
    else
      throwError "expected A & B (Prod), got {← ppExpr goal}"

def matchIdxProduct (goal : Expr) : MetaM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``IdxProduct, #[_, x, f]) => return (x, f)
  | _ => throwError "expected &[x ∈ X] F x (IdxProduct), got {← ppExpr goal}"

def matchIdxCoproduct (goal : Expr) : MetaM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``IdxCoproduct, #[_, x, f]) => return (x, f)
  | _ => throwError "expected ⊕[x ∈ X] F x (IdxCoproduct), got {← ppExpr goal}"

private def getInductiveVal (env : Lean.Environment) (name : Lean.Name) : Option Lean.InductiveVal :=
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

/-- Count the number of Splitting binders in a ctor type after the `w` parameter.
    Returns 0 if not tensor-flattened. -/
def countTensorSplittings (cfg : ElabConfig) (goal : Expr) (fullCtorName : Name)
    : TermElabM Nat := do
  let some (ty, _, _) ← instantiateCtorFull cfg goal fullCtorName | return 0
  withLocalDecl `w .default cfg.stringTy fun w => do
    -- ty: ∀ (w : String), ... → RetTy w
    match ty with
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
  -- body should be: ∀ (s : Splitting prev), compTy s.left → rest...
  match body with
  | .forallE _ splitTy afterS _ =>
    let splitTyW ← whnf splitTy
    if splitTyW.getAppFn.isConstOf ``Splitting then
      -- This is a splitting binder → tensor component
      let splitE ← mkAppM ``Tensor.split #[tExpr]
      let fstE ← mkAppM ``Tensor.fst #[tExpr]
      -- Skip past (s : Splitting _) and (a : compTy s.left)
      -- Peek at what comes after the component binder
      let sVar ← mkFreshExprMVar (some splitTyW)
      let afterSInst := afterS.instantiate1 sVar
      match afterSInst with
      | .forallE _ _ rest _ =>
        let dummy ← mkFreshExprMVar none
        let restBody := rest.instantiate1 dummy
        -- Check if there's another Splitting after this
        match restBody with
        | .forallE _ nextSplitTy _ _ =>
          let nextSplitTyW ← whnf nextSplitTy
          if nextSplitTyW.getAppFn.isConstOf ``Splitting then
            -- More tensor components: recurse into .snd
            let sndE ← mkAppM ``Tensor.snd #[tExpr]
            let innerArgs ← decomposeTensorForCtor sndE restBody
            return #[splitE, fstE] ++ innerArgs
          else
            -- Last component (not a Splitting) → this is the rightmost element
            let sndE ← mkAppM ``Tensor.snd #[tExpr]
            return #[splitE, fstE, sndE]
        | _ =>
          -- No more foralls → this is the return type, so snd is last component
          let sndE ← mkAppM ``Tensor.snd #[tExpr]
          return #[splitE, fstE, sndE]
      | _ => throwError "unexpected tensor ctor shape in decomposeTensorForCtor"
    else
      -- Not a splitting → shouldn't happen for tensor ctors
      return #[tExpr]
  | _ => return #[tExpr]

/-- CPS helper for rec branches of tensor-flattened constructors.
    Walks the ctor type body (after params + w), introduces `withLocalDecl` for each
    splitting and component variable, and builds the reconstructed tensor value from inside out.
    Calls `k` with (all introduced fvars, tensor value, tensor grammar). -/
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
          -- Check if rest starts with another Splitting (more tensor components)
          match restInst with
          | .forallE _ nextSplitTy _ _ =>
            let nextSplitTyW ← whnf nextSplitTy
            if nextSplitTyW.getAppFn.isConstOf ``Splitting then
              -- Recurse into more tensor components
              withTensorCtorBinders cfg restInst fun innerFvars innerVal innerGram => do
                let tensorVal ← mkAppM ``Tensor.mk #[sVar, aVar, innerVal]
                let tensorGram ← mkAppM ``Tensor #[leftGram, innerGram]
                k (#[sVar, aVar] ++ innerFvars) tensorVal tensorGram
            else
              -- Last component: `restInst` is `rightTy → RetTy`
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

/-- CPS helper for multi-arity rec patterns. Walks a tensor-flattened ctor type (after params + w),
    introducing `withLocalDecl` for each splitting and component variable.
    Calls `k` with (all fvars, array of (grammar, strExpr, parseExpr) per component). -/
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
              -- More tensor components: recurse
              withTensorCtorComponents cfg restInst fun innerFvars innerComps => do
                k (#[sVar, aVar] ++ innerFvars) (#[comp] ++ innerComps)
            else
              -- Last component
              withLocalDecl `b .default nextSplitTy fun bVar => do
                let rightGram ← withLocalDecl `ww .default cfg.stringTy fun ww => do
                  abstractGrammarReplace ww nextSplitTy sRight
                let lastComp := (rightGram, sRight, bVar)
                k #[sVar, aVar, bVar] #[comp, lastComp]
          | _ =>
            throwError "withTensorCtorComponents: unexpected shape after component"
      | _ => throwError "withTensorCtorComponents: expected component after Splitting"
  | _ => throwError "withTensorCtorComponents: expected forallE with Splitting"

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
  registerLinearCtxInfo stx ctx start stop aliases goal
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
        if ← isDefEq (mkApp alias.projGrammar w) (mkApp goal w) then
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
        if ← isDefEq (mkApp v.grammar w) (mkApp goal w) then
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

  -- ─── Sorry ───────���────────────────────────────────────
  | `(gterm| sorry) => do
    let w ← concatStrs cfg ctx start stop
    mkSorry (mkApp goal w) (synthetic := true)

  -- ─── Tensor pair ────────────────────────────────────────
  | `(gterm| ($t₁, $t₂)) => do
    let (goalA, goalB) ← matchTensor cfg goal
    let k ← findSplit t₁ t₂ ctx start stop aliases
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
        let newCtx := ctx[0:start].toArray ++ #[newVar] ++ ctx[start:stop].toArray ++ ctx[stop:ctx.size].toArray
        let bodyExpr ← elaborateOrderedTerm cfg body newCtx start (stop + 1) goalB aliases
        mkLambdaFVars #[wPrime, vExpr] bodyExpr

  -- ─── Left lambda ────────────────────────────────────────
  | `(gterm| funL ($x:ident : $tyStx) => $body) => do
    let (goalB, goalA) ← matchLinFunL goal
    let _tyExpr ← Lean.Elab.Term.elabTerm tyStx none
    withLocalDecl `w' .default cfg.stringTy fun wPrime => do
      let vTy ← whnf (mkApp goalA wPrime)
      withLocalDecl x.getId .default vTy fun vExpr => do
        let newVar : OrderedVar := ⟨x.getId, goalA, wPrime, vExpr⟩
        let newCtx := ctx[0:start].toArray ++ ctx[start:stop].toArray ++ #[newVar] ++ ctx[stop:ctx.size].toArray
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
        -- Try constructor (single-arg or multi-arg)
        if let some fullCtorName ← tryResolveCtorName cfg goal name then
          if allArgs.size == 1 then
            -- Single arg: existing fold behavior
            let foldStx ← `(gterm| fold $c $(allArgs[0]!))
            return ← elaborateOrderedTerm cfg foldStx ctx start stop goal aliases
          else
            -- Multi-arg constructor: build right-nested pair and fold
            let nSplittings ← countTensorSplittings cfg goal fullCtorName
            if nSplittings == 0 then
              throwError "constructor '{name}' takes 1 argument, got {allArgs.size}"
            let expectedArgs := nSplittings + 1
            if allArgs.size != expectedArgs then
              throwError "constructor '{name}' expects {expectedArgs} arguments, got {allArgs.size}"
            -- Build right-nested pair: (a₁, (a₂, (a₃, a₄)))
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
    let isRightApp : Bool := match aPositions.back?, fPositions[0]? with
      | some am, some fm => am < fm
      | none, _          => true
      | _, none           => false
    let gramTy ← mkGrammarTy cfg
    if isRightApp == true then
      let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
      let fGoal ← mkAppM ``FunctionR #[mA, goal]
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
    else
      let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
      let fGoal ← mkAppM ``FunctionL #[goal, mA]
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
    if stx.raw.getKind == `recGterm || stx.raw.getKind == `LambekD.Elab.recGterm then
      let t : TSyntax `gterm := ⟨stx.raw[1]⟩
      let branches := stx.raw[3].getArgs
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
      -- Motive: fun (w_mot : String) (_ : IndTy w_mot) => goal(before ++ w_mot ++ after)
      -- where before/after are the context strings outside the scrutinee range.
      let motive ← withLocalDecl `w_mot .default cfg.stringTy fun wMot => do
        let indTyMot ← whnf (mkApp tGoalResolved wMot)
        withLocalDecl `t_mot .default indTyMot fun tMot => do
          -- Build full string with wMot replacing scrutinee's portion
          let mut motiveStr := wMot
          if tStop < stop then
            let afterStr ← concatStrs cfg ctx tStop stop
            motiveStr ← mkAppM ``HAppend.hAppend #[motiveStr, afterStr]
          for i in List.range (tStart - start) do
            let idx := tStart - 1 - i
            motiveStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, motiveStr]
          mkLambdaFVars #[wMot, tMot] (mkApp goal motiveStr)
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
      -- Build branch lambdas for each constructor
      -- Each branch lambda starts with (w : String) since w is an index
      let mut branchLams : Array Expr := #[]
      for branch in branches do
        let ctorName := branch[1].getId
        let varIdents := branch[2].getArgs  -- ident+ gives a null node of idents
        let body : TSyntax `gterm := ⟨branch[4]⟩
        let fullCtorName := indName ++ ctorName
        let isTensor ← isTensorCtor cfg tGoalResolved fullCtorName
        let cty ← instantiateCtorParams fullCtorName
        -- cty: ∀ (w : String), ... → IndTy w
        -- Branch lambda starts with (w : String)
        let lam ← withLocalDecl `w_br .default cfg.stringTy fun wBr => do
          match cty with
          | .forallE _ _ afterW _ =>
            let afterWInst := afterW.instantiate1 wBr
            if isTensor && varIdents.size > 1 then
              -- Multi-arity pattern: use single tensor var + nested let decomposition
              withTensorCtorBinders cfg afterWInst fun fvars tensorVal tensorGram => do
                let tensorName := Name.mkSimple s!"_tensor"
                let tensorOV : OrderedVar := ⟨tensorName, tensorGram, wBr, tensorVal⟩
                let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[tensorOV]
                -- Build nested let-tensor: let (v0, _r0) = _t in let (v1, _r1) = _r0 in ... let (vN-2, vN-1) = _rN-3 in body
                let names := varIdents.map (·.getId)
                let n := names.size
                let mut innerBody : TSyntax `gterm := body
                for j in List.range (n - 1) do
                  let i := n - 2 - j  -- iterate from innermost to outermost
                  let leftName := names[i]!
                  let rightName := if i == n - 2 then names[n - 1]! else Name.mkSimple s!"_rest{i}"
                  let scrutName := if i == 0 then tensorName else Name.mkSimple s!"_rest{i - 1}"
                  let leftIdent := mkIdent leftName
                  let rightIdent := mkIdent rightName
                  let scrutGterm ← `(gterm| $(mkIdent scrutName):ident)
                  innerBody ← `(gterm| let ($leftIdent, $rightIdent) = $scrutGterm in $innerBody)
                let branchExpr ← elaborateOrderedTerm cfg innerBody newCtx newStart newStop goal aliases
                mkLambdaFVars (#[wBr] ++ fvars) branchExpr
            else if isTensor then
              -- Single-var tensor pattern: existing behavior
              let varName := varIdents[0]!.getId
              withTensorCtorBinders cfg afterWInst fun fvars tensorVal tensorGram => do
                let tensorOV : OrderedVar := ⟨varName, tensorGram, wBr, tensorVal⟩
                let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[tensorOV]
                let branchExpr ← elaborateOrderedTerm cfg body newCtx newStart newStop goal aliases
                mkLambdaFVars (#[wBr] ++ fvars) branchExpr
            else
              -- Simple: ArgTy w → IndTy w
              if varIdents.size != 1 then
                throwError "non-tensor constructor '{ctorName}' takes 1 argument, but pattern has {varIdents.size} variables"
              let varName := varIdents[0]!.getId
              match afterWInst with
              | .forallE _ argTy _ _ =>
                let argGrammar ← withLocalDecl `ww .default cfg.stringTy fun ww => do
                  abstractGrammarReplace ww argTy wBr
                withLocalDecl varName .default argTy fun argVar => do
                  let argOV : OrderedVar := ⟨varName, argGrammar, wBr, argVar⟩
                  let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[argOV]
                  let branchExpr ← elaborateOrderedTerm cfg body newCtx newStart newStop goal aliases
                  mkLambdaFVars #[wBr, argVar] branchExpr
              | _ => throwError "unexpected ctor shape"
          | _ => throwError "unexpected ctor shape (no w binder)"
        branchLams := branchLams.push lam
      let casesOnName := indName ++ `casesOn
      -- casesOn signature: {params...} → {motive} → {indices...} → (target) → branches...
      let mut args : Array (Option Expr) := paramsOnly.toArray.map some
      args := args.push (some motive)  -- motive
      args := args.push none           -- w index (inferred from tExpr)
      args := args.push (some tExpr)   -- target
      for lam in branchLams do
        args := args.push (some lam)
      let casesResult ← mkAppOptM casesOnName args
      -- casesOn returns goal(before ++ wT ++ after). If the scrutinee is a single
      -- context position, this is definitionally equal to goal(concatStrs ctx start stop).
      -- For multi-position scrutinees, we may need an associativity cast.
      let fullStr ← concatStrs cfg ctx start stop
      let mut motiveResultStr := wT
      if tStop < stop then
        let afterStr ← concatStrs cfg ctx tStop stop
        motiveResultStr ← mkAppM ``HAppend.hAppend #[motiveResultStr, afterStr]
      for i in List.range (tStart - start) do
        let idx := tStart - 1 - i
        motiveResultStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, motiveResultStr]
      if ← isDefEq motiveResultStr fullStr then
        return casesResult
      else
        let strEq ← proveStrEq motiveResultStr fullStr
        let goalEq ← mkAppM ``congrArg #[goal, strEq]
        mkAppM ``cast #[goalEq, casesResult]
    else
      throwError "unsupported gterm syntax: {stx}"

-- ═══════════════════════════════════════════════════════════
-- Multi-pattern entry point: [| pat₁ pat₂ ... => body |]
-- ═══════════════════════════════════════════════════════════

declare_syntax_cat gpat
syntax ident : gpat
syntax "(" ident ":" term ")" : gpat
syntax "⟨" gpat ", " gpat "⟩" : gpat

syntax "[|" gpat+ " => " gterm "|]" : term

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
    -- Multiple patterns: decompose grammar as A ⊗ Rest
    let (gramA, gramRest) ← matchTensor cfg grammar
    -- Build motive for elimTensor: fun s => goal (ctx_prefix ++ s)
    let motiveC ← withLocalDecl `s .default cfg.stringTy fun s => do
      let mut fullStr := s
      -- Prepend already-bound context strings from right to left
      for i in List.range ctx.size do
        let idx := ctx.size - 1 - i
        fullStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, fullStr]
      mkLambdaFVars #[s] (mkApp goal fullStr)
    -- Introduce wL, wR, aVar, restVar
    withLocalDecl `wL .default cfg.stringTy fun wL => do
    withLocalDecl `wR .default cfg.stringTy fun wR => do
      let aTy ← whnf (mkApp gramA wL)
      let restTy ← whnf (mkApp gramRest wR)
      withLocalDecl `_a .default aTy fun aVar => do
      withLocalDecl `_rest .default restTy fun restVar => do
        -- Process first pattern, then recurse on remaining patterns
        let firstPat := pats[0]!
        let remainingPats := pats[1:]
        let bodyExpr ← elaborateSinglePatternCPS cfg firstPat gramA wL aVar ctx aliases
          fun newCtx newAliases => do
            elaborateMultiPatterns cfg remainingPats.toArray gramRest wR restVar
              newCtx newAliases goal body
        let bodyLam ← mkLambdaFVars #[wL, wR, aVar, restVar] bodyExpr
        mkAppM ``elimTensor #[motiveC, parseExpr, bodyLam]

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
    let gramA ← mkLambdaFVars #[w] aw
    let gramB ← mkLambdaFVars #[w] bw
    withLocalDecl `v .default aw fun v => do
      let bodyExpr ← elaborateMultiPatterns cfg pats gramA w v #[] {} gramB body
      mkLambdaFVars #[w, v] bodyExpr

end LambekD.Elab
