import Lean
import LambekD.Core.Base

/-!
# Elaborator base types

Core data structures for the ordered linear DSL elaborator:
OrderedVar, OrderedCtx, Alias, AliasMap, ElabConfig.
-/

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

/-- Info for resolving recursive calls inside `rec d as f of` branches.
    Maps sub-term variable names to their induction hypothesis expressions. -/
structure RecCallInfo where
  recName : Name
  ihMap   : Std.HashMap Name Expr

structure ElabConfig where
  stringTy : Expr      -- The string type (e.g., `List Paren`)
  alphabetTy : Expr    -- The alphabet type (e.g., `Paren`)
  gramLevel : Level     -- The universe level of Grammar (e.g., `0`)
  recInfo : Option RecCallInfo := none  -- set inside `rec ... as f of` branches

end LambekD.Elab
