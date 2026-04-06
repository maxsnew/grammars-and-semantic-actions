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

end LambekD.Elab
