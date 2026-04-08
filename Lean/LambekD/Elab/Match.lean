import LambekD.Elab.Util

/-!
# Grammar type matching for the elaborator

Functions to decompose grammar goals into their connective components:
matchTensor, matchLinFunR/L, matchSum, matchProd, matchIdxProduct/Coproduct.
-/

namespace LambekD.Elab

open Lean Elab Term Meta
open LambekD

def matchTensor (cfg : ElabConfig) (goal : Expr) : TermElabM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``GTensor, #[_, a, b]) => return (a, b)
  | _ =>
    -- Handle metavar goals by unifying with GTensor ?A ?B
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy)
    let mB ← mkFreshExprMVar (some gramTy)
    let tGoal ← mkAppM ``GTensor #[mA, mB]
    if ← isDefEq goal tGoal then
      return (← instantiateMVars mA, ← instantiateMVars mB)
    else
      throwError "expected A ⊗ B (GTensor), got {← ppExpr goal}"

def matchLinFunR (goal : Expr) : MetaM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``GFunctionR, #[_, a, b]) => return (a, b)
  | _ => throwError "expected A ⊸ B (GFunctionR), got {← ppExpr goal}"

def matchLinFunL (goal : Expr) : MetaM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``GFunctionL, #[_, b, a]) => return (b, a)
  | _ => throwError "expected B ⟜ A (GFunctionL), got {← ppExpr goal}"

def matchSum (cfg : ElabConfig) (goal : Expr) : TermElabM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``GSum, #[_, a, b]) => return (a, b)
  | _ =>
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy)
    let mB ← mkFreshExprMVar (some gramTy)
    let sGoal ← mkAppM ``GSum #[mA, mB]
    if ← isDefEq goal sGoal then
      return (← instantiateMVars mA, ← instantiateMVars mB)
    else
      throwError "expected A ⊕ B (GSum), got {← ppExpr goal}"

def matchProd (cfg : ElabConfig) (goal : Expr) : TermElabM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``GProduct, #[_, a, b]) => return (a, b)
  | _ =>
    let gramTy ← mkGrammarTy cfg
    let mA ← mkFreshExprMVar (some gramTy)
    let mB ← mkFreshExprMVar (some gramTy)
    let pGoal ← mkAppM ``GProduct #[mA, mB]
    if ← isDefEq goal pGoal then
      return (← instantiateMVars mA, ← instantiateMVars mB)
    else
      throwError "expected A & B (GProduct), got {← ppExpr goal}"

def matchIdxProduct (goal : Expr) : MetaM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``GIdxProduct, #[_, x, f]) => return (x, f)
  | _ => throwError "expected &[x ∈ X] F x (GIdxProduct), got {← ppExpr goal}"

def matchIdxCoproduct (goal : Expr) : MetaM (Expr × Expr) := do
  let g ← etaReduceGrammar goal
  match g.getAppFnArgs with
  | (``GIdxCoproduct, #[_, x, f]) => return (x, f)
  | _ => throwError "expected ⊕[x ∈ X] F x (GIdxCoproduct), got {← ppExpr goal}"

end LambekD.Elab
