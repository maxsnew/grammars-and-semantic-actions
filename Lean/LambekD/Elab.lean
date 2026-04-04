import Lean

namespace LambekD

universe uAlph uGram uIntuit
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

def splitting (l r : String) : Splitting (l ++ r) := ⟨l, r, rfl⟩

structure Tensor (A B : Grammar) (w : String) where
  split : Splitting w
  fst : A split.left
  snd : B split.right

def Epsilon : Grammar := fun w => PLift (w = [])
def Literal (c : Alphabet) : Grammar := fun w => PLift (w = [c])
def FunctionR (A B : Grammar) : Grammar := fun w => ∀ w', A w' → B (w' ++ w)
def FunctionL (B A : Grammar) : Grammar := fun w => ∀ w', A w' → B (w ++ w')
def Sum (A B : Grammar) : Grammar := fun w => A w ⊕ B w
def Product (A B : Grammar) : Grammar := fun w => A w × B w
def Top : Grammar := fun _ => PUnit
def Bottom : Grammar := fun _ => PEmpty
def IdxProduct (X : Type uIntuit) (F : X → Grammar) : Grammar := fun w => ∀ x, F x w
def IdxCoproduct (X : Type uIntuit) (F : X → Grammar) : Grammar := fun w => Σ x, F x w

def GrammarTerm (A B : Grammar) := ∀ w, A w → B w

scoped infixr:70 " ⊗ "  => Tensor
scoped infixr:60 " ⊸ "  => FunctionR
scoped infixl:60 " ⟜ "  => FunctionL
scoped infixl:65 " ⊕ "  => Sum
scoped infixl:70 " & "  => Product
scoped infixl:25 " ⊢ "  => GrammarTerm
-- TODO notation for IdxProduct, IdxCoproduct, Top, Bottom, Literal
-- IdxProduct should be like a pi type. Use syntax like &[ x ∈ X ] F x
-- similarly for IdxCoproduct
-- Top should be notated ⊤, Bottom ⊥
-- Literal should be some sort of quotation or lifting operation on the alphabet. "c" or smth, but it can't clash with Lean's primitive string literals

def elimTensor {A B : Grammar} (C : String → Sort _) {w : String}
    (t : Tensor A B w) (body : (wL wR : String) → A wL → B wR → C (wL ++ wR))
    : C w := t.split.eq ▸ body t.split.left t.split.right t.fst t.snd

def elimEpsilon (C : String → Sort _) {w : String}
    (t : Epsilon w) (body : C []) : C w := t.down ▸ body

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

structure ElabConfig where
  stringTy : Expr      -- The string type (e.g., `List Paren`)
  alphabetTy : Expr    -- The alphabet type (e.g., `Paren`)

declare_syntax_cat gterm

syntax ident : gterm
syntax "ε" : gterm
syntax "tt" : gterm
syntax "(" gterm ", " gterm ")" : gterm
syntax "let" "(" ident ", " ident ")" "=" gterm "in" gterm : gterm
syntax "let" "⟨⟩" "=" gterm "in" gterm : gterm
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
syntax "(" gterm ")" : gterm
syntax "[|" gterm "|]" : term

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
    : TermElabM Nat := do
  let leftNames  := collectAllIdents leftStx
  let rightNames := collectAllIdents rightStx
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
    : TermElabM (Nat × Nat) := do
  let names := collectAllIdents stx
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

def mkGrammarTy (cfg : ElabConfig) : MetaM Expr :=
  mkArrow cfg.stringTy (mkSort (.succ .zero))

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

partial def elaborateOrderedTerm
    (cfg : ElabConfig)
    (stx : TSyntax `gterm)
    (ctx : OrderedCtx)
    (start stop : Nat)
    (goal : Expr)
    : TermElabM Expr := do
  withRef stx do
  match stx with

  -- ─── Variable ───────────────────────────────────────────
  | `(gterm| $x:ident) => do
    let name := x.getId
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
    mkAppM ``PLift.up #[rflExpr]

  -- ─── Top ────────────────────────────────────────────────
  | `(gterm| tt) => do
    if start != stop then
      let unused := (List.range (stop - start)).map (fun i => (ctx.getV (start + i)).userName)
      throwError "linear variable(s) {unused} unused in tt"
    return mkConst ``PUnit.unit

  -- ─── Tensor pair ────────────────────────────────────────
  | `(gterm| ($t₁, $t₂)) => do
    let (goalA, goalB) ← matchTensor cfg goal
    let k ← findSplit t₁ t₂ ctx start stop
    let e₁ ← elaborateOrderedTerm cfg t₁ ctx start k goalA
    let e₂ ← elaborateOrderedTerm cfg t₂ ctx k stop goalB
    let wLeft ← concatStrs cfg ctx start k
    let wRight ← concatStrs cfg ctx k stop
    let wFull ← concatStrs cfg ctx start stop
    let sp ← mkAppM ``LambekD.splitting #[wLeft, wRight]
    let tensor ← mkAppM ``Tensor.mk #[sp, e₁, e₂]
    -- tensor : goal (wLeft ++ wRight). Cast to goal wFull if they differ.
    let wLR ← mkAppM ``HAppend.hAppend #[wLeft, wRight]
    if ← isDefEq wLR wFull then
      return tensor
    else
      let strEq ← proveStrEq wLR wFull
      let goalEq ← mkAppM ``congrArg #[goal, strEq]
      mkAppM ``cast #[goalEq, tensor]

  -- ─── Let-tensor ─────────────────────────────────────────
  --
  -- Given `let (a, b) = t in body` where `t : Tensor A B wT`:
  -- 1. Compute right-assoc motive C = fun s => goal (w_s ++ (... ++ (w_{tS-1} ++ (s ++ wAfter))))
  -- 2. Introduce fresh `wL`, `wR`, `a : A wL`, `b : B wR`
  -- 3. Elaborate body in the updated context
  -- 4. If there's an after-context, cast body via List.append_assoc
  -- 5. Abstract to get `fun wL wR a b => bodyExpr`
  -- 6. Apply `elimTensor C tExpr (fun wL wR a b => bodyExpr)`
  --
  | `(gterm| let ($a:ident, $b:ident) = $t in $body) => do
    let (tStart, tStop) ← locateVars t ctx start stop
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
    let mB ← mkFreshExprMVar (some gramTy) .natural `goalB
    let tGoal ← mkAppM ``Tensor #[mA, mB]
    let tExpr ← elaborateOrderedTerm cfg t ctx tStart tStop tGoal
    let gramA ← instantiateMVars mA
    let gramB ← instantiateMVars mB
    let hasAfter := tStop < stop
    -- Compute right-associated motive C:
    --   fun s => goal (w_s ++ (... ++ (w_{tS-1} ++ (s ++ wAfter))))
    -- This matches how concatStrs (right-folded) builds the full string.
    let wAfter ← concatStrs cfg ctx tStop stop
    let motiveC ← withLocalDecl `s .default cfg.stringTy fun s => do
      let mut fullStr := s
      if hasAfter then
        fullStr ← mkAppM ``HAppend.hAppend #[fullStr, wAfter]
      -- Prepend before-variables one by one from right to left
      for i in List.range (tStart - start) do
        let idx := tStart - 1 - i
        fullStr ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, fullStr]
      mkLambdaFVars #[s] (mkApp goal fullStr)
    -- Introduce wL, wR as local string variables
    withLocalDecl `wL .default cfg.stringTy fun wL => do
    withLocalDecl `wR .default cfg.stringTy fun wR => do
      let aTy ← whnf (mkApp gramA wL)
      let bTy ← whnf (mkApp gramB wR)
      withLocalDecl a.getId .default aTy fun aVar => do
      withLocalDecl b.getId .default bTy fun bVar => do
        let aOV : OrderedVar := ⟨a.getId, gramA, wL, aVar⟩
        let bOV : OrderedVar := ⟨b.getId, gramB, wR, bVar⟩
        let (newCtx, newStart, newStop) := replaceSlice ctx start stop tStart tStop #[aOV, bOV]
        let bodyExpr ← elaborateOrderedTerm cfg body newCtx newStart newStop goal
        -- When there's context after the tensor, the body's string is right-associated:
        --   wL ++ (wR ++ wAfter)
        -- but the motive at (wL ++ wR) gives:
        --   (wL ++ wR) ++ wAfter
        -- Cast using List.append_assoc.
        let finalBody ← if hasAfter then do
          -- Build prefix function: fun x => goal (w_s ++ (... ++ (w_{tS-1} ++ x)))
          -- When tStart == start, this is just `goal` itself.
          let prefixFn ← if tStart > start then
            withLocalDecl `x .default cfg.stringTy fun x => do
              let mut result := x
              for i in List.range (tStart - start) do
                let idx := tStart - 1 - i
                result ← mkAppM ``HAppend.hAppend #[(ctx.getV idx).strExpr, result]
              mkLambdaFVars #[x] (mkApp goal result)
          else
            pure goal
          -- assocProof : (wL ++ wR) ++ wAfter = wL ++ (wR ++ wAfter)
          let assocProof ← mkAppM ``List.append_assoc #[wL, wR, wAfter]
          -- congrArg prefixFn assocProof : prefixFn ((wL++wR)++wAfter) = prefixFn (wL++(wR++wAfter))
          let congr ← mkAppM ``congrArg #[prefixFn, assocProof]
          -- Eq.mpr congr bodyExpr : prefixFn ((wL++wR)++wAfter)  [= C(wL++wR)]
          mkAppM ``Eq.mpr #[congr, bodyExpr]
        else
          pure bodyExpr
        let bodyLam ← mkLambdaFVars #[wL, wR, aVar, bVar] finalBody
        mkAppM ``elimTensor #[motiveC, tExpr, bodyLam]

  -- ─── Let-unit ───────────────────────────────────────────
  | `(gterm| let ⟨⟩ = $t in $body) => do
    let (tStart, tStop) ← locateVars t ctx start stop
    let epsConst ← mkAppM ``Epsilon #[]
    let tExpr ← elaborateOrderedTerm cfg t ctx tStart tStop epsConst
    -- Compute right-associated motive C for elimEpsilon
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
    let bodyExpr ← elaborateOrderedTerm cfg body newCtx newStart newStop goal
    mkAppM ``elimEpsilon #[motiveC, tExpr, bodyExpr]

  -- ─── Right lambda ───────────────────────────────────────
  | `(gterm| fun ($x:ident : $tyStx) => $body) => do
    let (goalA, goalB) ← matchLinFunR goal
    let _tyExpr ← Lean.Elab.Term.elabTerm tyStx none
    withLocalDecl `w' .default cfg.stringTy fun wPrime => do
      let vTy ← whnf (mkApp goalA wPrime)
      withLocalDecl x.getId .default vTy fun vExpr => do
        let newVar : OrderedVar := ⟨x.getId, goalA, wPrime, vExpr⟩
        let newCtx := ctx[0:start].toArray ++ #[newVar] ++ ctx[start:stop].toArray ++ ctx[stop:ctx.size].toArray
        let bodyExpr ← elaborateOrderedTerm cfg body newCtx start (stop + 1) goalB
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
        let bodyExpr ← elaborateOrderedTerm cfg body newCtx start (stop + 1) goalB
        mkLambdaFVars #[wPrime, vExpr] bodyExpr

  -- ─── Application ────────────────────────────────────────
  | `(gterm| $f $a) => do
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
      -- Right-app: arg LEFT of function. Result: eF wA eA : goal (wA ++ wF)
      let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
      let fGoal ← mkAppM ``FunctionR #[mA, goal]
      let k ← findSplit a f ctx start stop
      let eA ← elaborateOrderedTerm cfg a ctx start k mA
      let eF ← elaborateOrderedTerm cfg f ctx k stop fGoal
      let wA ← concatStrs cfg ctx start k
      let result ← mkAppM' eF #[wA, eA]
      -- result : goal (wA ++ wF). Cast to goal wFull if they differ.
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
      -- Left-app: function LEFT of arg. Result: eF wA eA : goal (wF ++ wA)
      let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
      let fGoal ← mkAppM ``FunctionL #[goal, mA]
      let k ← findSplit f a ctx start stop
      let eF ← elaborateOrderedTerm cfg f ctx start k fGoal
      let eA ← elaborateOrderedTerm cfg a ctx k stop mA
      let wA ← concatStrs cfg ctx k stop
      let result ← mkAppM' eF #[wA, eA]
      -- result : goal (wF ++ wA). Cast if needed.
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
    let e₁ ← elaborateOrderedTerm cfg t₁ ctx start stop goalA
    let e₂ ← elaborateOrderedTerm cfg t₂ ctx start stop goalB
    mkAppM ``Prod.mk #[e₁, e₂]

  -- ─── Projections ────────────────────────────────────────
  | `(gterm| fst $t) => do
    let gramTy ← mkGrammarTy cfg
    let mB ← mkFreshExprMVar (some gramTy) .natural `goalB
    let tGoal ← mkAppM ``Product #[goal, mB]
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop tGoal
    mkAppM ``Prod.fst #[tExpr]

  | `(gterm| snd $t) => do
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
    let tGoal ← mkAppM ``Product #[mA, goal]
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop tGoal
    mkAppM ``Prod.snd #[tExpr]

  -- ─── Injections ─────────────────────────────────────────
  | `(gterm| inl $t) => do
    let (goalA, goalB) ← matchSum cfg goal
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop goalA
    let w ← concatStrs cfg ctx start stop
    let bw := mkApp goalB w
    mkAppOptM ``Sum.inl #[none, some bw, some tExpr]

  | `(gterm| inr $t) => do
    let (goalA, goalB) ← matchSum cfg goal
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop goalB
    let w ← concatStrs cfg ctx start stop
    let aw := mkApp goalA w
    mkAppOptM ``Sum.inr #[some aw, none, some tExpr]

  -- ─── Case ───────────────────────────────────────────────
  | `(gterm| case $t of | inl $x:ident => $u₁ | inr $y:ident => $u₂) => do
    let (tStart, tStop) ← locateVars t ctx start stop
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy) .natural `goalA
    let mB ← mkFreshExprMVar (some gramTy) .natural `goalB
    let tGoal ← mkAppM ``Sum #[mA, mB]
    let tExpr ← elaborateOrderedTerm cfg t ctx tStart tStop tGoal
    let gramA ← instantiateMVars mA
    let gramB ← instantiateMVars mB
    let wT ← concatStrs cfg ctx tStart tStop
    let aTy ← whnf (mkApp gramA wT)
    let bTy ← whnf (mkApp gramB wT)
    let u₁Lam ← withLocalDecl x.getId .default aTy fun aVar => do
      let aOV : OrderedVar := ⟨x.getId, gramA, wT, aVar⟩
      let (ctxL, startL, stopL) := replaceSlice ctx start stop tStart tStop #[aOV]
      let e ← elaborateOrderedTerm cfg u₁ ctxL startL stopL goal
      mkLambdaFVars #[aVar] e
    let u₂Lam ← withLocalDecl y.getId .default bTy fun bVar => do
      let bOV : OrderedVar := ⟨y.getId, gramB, wT, bVar⟩
      let (ctxR, startR, stopR) := replaceSlice ctx start stop tStart tStop #[bOV]
      let e ← elaborateOrderedTerm cfg u₂ ctxR startR stopR goal
      mkLambdaFVars #[bVar] e
    -- Build: Sum.casesOn (motive := fun _ => goalW) tExpr u₁Lam u₂Lam
    let w ← concatStrs cfg ctx start stop
    let goalW := mkApp goal w
    -- Get the value-level sum type (A w ⊕ B w) by inferring tExpr's type.
    -- We can't use ``Sum here because it resolves to LambekD.Sum (grammar-level).
    let sumTy ← whnf (← inferType tExpr)
    -- motive: fun (_ : A w ⊕ B w) => goal w
    let motive := .lam `_ sumTy goalW .default
    mkAppOptM ``Sum.casesOn #[some aTy, some bTy, some motive, some tExpr, some u₁Lam, some u₂Lam]

  -- ─── Absurd ─────────────────────────────────────────────
  | `(gterm| absurd $t) => do
    let botConst ← mkAppM ``Bottom #[]
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop botConst
    mkAppM ``PEmpty.elim #[tExpr]

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
    let tExpr ← elaborateOrderedTerm cfg t ctx start stop gramA
    let w ← concatStrs cfg ctx start stop
    mkAppM' fExpr #[w, tExpr]

  | `(gterm| ($t)) => elaborateOrderedTerm cfg t ctx start stop goal

  | _ => throwError "unsupported gterm syntax: {stx}"

elab "[|" body:gterm "|]" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let expectedType ← whnf expectedType
  let .forallE _ domTy body₁ _ := expectedType
    | throwError "[| ... |]: expected type ∀ w, A w → B w, got {expectedType}"
  -- domTy is the string type (e.g., List Paren)
  let stringTy := domTy
  -- Extract alphabet type from List α
  let stringTyW ← whnf stringTy
  let alphabetTy ← match stringTyW.getAppFnArgs with
    | (``List, #[α]) => pure α
    | _ => throwError "[| ... |]: expected string type List α, got {stringTy}"
  let cfg : ElabConfig := { stringTy, alphabetTy }
  withLocalDecl `w .default stringTy fun w => do
    let body₁Inst := body₁.instantiate1 w
    let body₁Inst ← whnf body₁Inst
    let .forallE _ aw bw _ := body₁Inst
      | throwError "[| ... |]: expected type ∀ w, A w → B w, got inner {body₁Inst}"
    let gramA ← mkLambdaFVars #[w] aw
    let gramB ← mkLambdaFVars #[w] bw
    withLocalDecl `v .default aw fun v => do
      let ctx : OrderedCtx := #[⟨`input, gramA, w, v⟩]
      let bodyExpr ← elaborateOrderedTerm cfg body ctx 0 1 gramB
      mkLambdaFVars #[w, v] bodyExpr

end LambekD.Elab
