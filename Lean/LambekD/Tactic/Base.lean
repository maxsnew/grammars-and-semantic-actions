import Lean
import LambekD.Core.Defs

/-!
# Proof automation for Lambek^D grammar theory

Tactics and simp sets for the common proof patterns in the grammar modules:
- `splitting_cases`: eliminate all `Splitting.eq` / `PLift` evidence via subst + cases
- `grammar_ext`: extensionality + destructuring + equality elimination for grammar morphisms
- `grammar_simp`: simp set for β/η laws, composition laws, and string lemmas
-/

namespace LambekD.Tactic

open Lean Elab Tactic Meta

-- ═══════════════════════════════════════════════════════════
-- splitting_cases
-- ═══════════════════════════════════════════════════════════

/-- Try to `subst` one equality hypothesis where one side is an fvar. -/
private def trySubstOne (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if let some (_, lhs, rhs) := ty.eq? then
      if rhs.isFVar then
        try
          let (_, g) ← substCore goal decl.fvarId (symm := false)
          return some g
        catch _ => pure ()
      if lhs.isFVar then
        try
          let (_, g) ← substCore goal decl.fvarId (symm := true)
          return some g
        catch _ => pure ()
  return none

/-- Repeatedly subst all equality hypotheses. -/
private partial def substAll (goal : MVarId) : MetaM MVarId := do
  match ← trySubstOne goal with
  | some g => substAll g
  | none => return goal

/-- Try to `cases` one PLift or remaining Eq hypothesis. -/
private def tryCasesOne (goal : MVarId) : MetaM (Option (Array MVarId)) := goal.withContext do
  let lctx ← getLCtx
  -- PLift first (epsilon/literal evidence)
  for decl in lctx do
    if decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if ty.isAppOf ``PLift || ty.isAppOf ``ULift then
      try return some ((← goal.cases decl.fvarId).map (·.mvarId))
      catch _ => continue
  -- Then Eq
  for decl in lctx do
    if decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if (ty.eq?).isSome then
      try return some ((← goal.cases decl.fvarId).map (·.mvarId))
      catch _ => continue
  return none

/-- Recursively subst + cases all equality and PLift hypotheses. -/
private partial def elimAll (goals : Array MVarId) : MetaM (Array MVarId) := do
  let mut result : Array MVarId := #[]
  for goal in goals do
    if ← goal.isAssigned then continue
    let goal ← substAll goal
    if ← goal.isAssigned then continue
    match ← tryCasesOne goal with
    | some gs => result := result ++ (← elimAll gs)
    | none => result := result.push goal
  return result

/-- `splitting_cases` eliminates all splitting equalities and PLift evidence,
    then tries `rfl` on remaining goals. -/
elab "splitting_cases" : tactic => do
  let goals ← getGoals
  let goals' ← elimAll goals.toArray
  let mut remaining : Array MVarId := #[]
  for g in goals' do
    if ← g.isAssigned then continue
    try g.refl
    catch _ => remaining := remaining.push g
  setGoals remaining.toList

-- ═══════════════════════════════════════════════════════════
-- grammar_ext
-- ═══════════════════════════════════════════════════════════

/-- Check if a type is a grammar structure we should destructure
    (Tensor, Splitting, PLift — possibly hidden behind Epsilon/Literal). -/
private def isGrammarStructTy (ty : Expr) : MetaM Bool := do
  if ty.isAppOf ``LambekD.Tensor || ty.isAppOf ``LambekD.Splitting || ty.isAppOf ``PLift || ty.isAppOf ``ULift then
    return true
  let ty' ← whnf ty
  return ty'.isAppOf ``LambekD.Tensor || ty'.isAppOf ``LambekD.Splitting || ty'.isAppOf ``PLift || ty'.isAppOf ``ULift

/-- Try to `cases` one hypothesis whose type is a grammar structure. -/
private def tryCasesStruct (goal : MVarId) : MetaM (Option (Array MVarId)) := goal.withContext do
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if ← isGrammarStructTy ty then
      try return some ((← goal.cases decl.fvarId).map (·.mvarId))
      catch _ => continue
  return none

/-- Repeatedly destruct all grammar structures (Tensor → Splitting + fields). -/
private partial def destructAll (goals : Array MVarId) : MetaM (Array MVarId) := do
  let mut result : Array MVarId := #[]
  for goal in goals do
    if ← goal.isAssigned then continue
    match ← tryCasesStruct goal with
    | some gs => result := result ++ (← destructAll gs)
    | none => result := result.push goal
  return result

/-- `grammar_ext` proves equalities of grammar morphisms by:
    1. `funext` to introduce string and parse-tree arguments
    2. Recursively destructuring Tensor/Splitting/PLift in the context
    3. Eliminating equalities via subst/cases
    4. Closing with `rfl` or `simp_all`

    Handles most grammar morphism equalities in one shot. For proofs
    involving ε unit inverse round-trips (where `simp at eq` is needed
    between destructuring steps), use the manual pattern instead. -/
elab "grammar_ext" : tactic => do
  evalTactic (← `(tactic| funext _ _))
  let goals ← getGoals
  let goals' ← destructAll goals.toArray
  let goals'' ← elimAll goals'
  setGoals goals''.toList
  evalTactic (← `(tactic| all_goals first | rfl | simp_all | skip))

-- ═══════════════════════════════════════════════════════════
-- grammar_simp
-- ═══════════════════════════════════════════════════════════

/-- Simp set for grammar morphism equational reasoning.
    Tag lemmas with `@[grammar_simp]` to include them. -/
register_simp_attr grammar_simp

-- ═══════════════════════════════════════════════════════════
-- grammar_decreasing
-- ═══════════════════════════════════════════════════════════

/-- Try to assert a Splitting length fact. -/
private def tryAssertSplittingFact (goal : MVarId) (decl : LocalDecl) : MetaM MVarId :=
  tryCatch
    (do let lengthEq ← mkAppM ``LambekD.Splitting.length_eq #[decl.toExpr]
        let lengthEqTy ← inferType lengthEq
        let (_, g) ← (← goal.assert `_h_split lengthEqTy lengthEq).intro1
        pure g)
    (fun _ => pure goal)

/-- Try to assert a Literal or Epsilon length fact. -/
private def tryAssertLitEpsFact (goal : MVarId) (decl : LocalDecl) (ty' : Expr) : MetaM MVarId := do
  let innerTy ← whnf ty'.getAppArgs.back!
  if !innerTy.isAppOf ``PLift then return goal
  let eqTy ← whnf innerTy.getAppArgs.back!
  let some (_, _, rhs) := eqTy.eq? | return goal
  let rhs' ← whnf rhs
  if !(rhs'.isAppOf ``List.cons || rhs'.isAppOf ``List.nil) then return goal
  for lemName in [``LambekD.Literal.length_eq, ``LambekD.Epsilon.length_eq] do
    let r ← tryCatch
      (do let proof ← mkAppM lemName #[decl.toExpr]
          let proofTy ← inferType proof
          let (_, g) ← (← goal.assert `_h_len proofTy proof).intro1
          pure (some g))
      (fun _ => pure none)
    if let some g := r then return g
  return goal

/-- Try to assert a length fact from a single hypothesis. Returns the updated goal. -/
private def tryAssertLengthFact (goal : MVarId) (decl : LocalDecl) : MetaM MVarId := do
  let ty ← instantiateMVars decl.type
  let ty' ← whnf ty
  if ty'.isAppOf ``LambekD.Splitting then
    return ← tryAssertSplittingFact goal decl
  if ty'.isAppOf ``ULift then
    return ← tryCatch (tryAssertLitEpsFact goal decl ty') (fun _ => pure goal)
  return goal

/-- Zeta-reduce all non-let hypothesis types to expand let-bound fvars. -/
private def zetaReduceHyps (goal : MVarId) : MetaM MVarId := goal.withContext do
  let lctx ← getLCtx
  let mut g := goal
  for decl in lctx do
    if decl.isAuxDecl || decl.isLet then continue
    let ty ← instantiateMVars decl.type
    let ty' ← Lean.Meta.zetaReduce ty
    if ty != ty' then
      g ← g.replaceLocalDeclDefEq decl.fvarId ty'
  return g

/-- Extract length facts from Splitting, Literal, and Epsilon hypotheses,
    then close with omega. Used in `decreasing_by` for recursive grammar
    definitions where termination follows from string length decrease. -/
elab "grammar_decreasing" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let lctx ← getLCtx
    let mut newGoal := goal
    for decl in lctx do
      if decl.isAuxDecl then continue
      newGoal ← tryAssertLengthFact newGoal decl
    newGoal ← substAll newGoal
    -- Zeta-reduce hypothesis types to normalize let-bound fvars
    newGoal ← zetaReduceHyps newGoal
    setGoals [newGoal]
    evalTactic (← `(tactic| simp only [List.length_append, List.length_cons, List.length_nil] at *))
    evalTactic (← `(tactic| omega))

end LambekD.Tactic
