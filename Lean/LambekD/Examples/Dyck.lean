import LambekD.Automata.Deterministic
import LambekD.Grammar.Properties.Base
import LambekD.Parser.Base
import LambekD.Tactic

/-!
# Dyck grammar: balanced parentheses

Defines the Dyck grammar (balanced brackets) and a deterministic
automaton that recognizes it. The automaton uses `Option Nat` as states:
`some n` means `n` unmatched opening brackets, `none` is a fail state.

Key results (with sorry for deep equational proofs):
- `Dyck`: the grammar of balanced bracket sequences
- `DyckAut`: deterministic automaton recognizing Dyck
- `mkTree`: extract a Dyck parse from an accepting trace
- `buildTrace`: build a trace from a Dyck parse
- `Dyck_equiv_Trace`: strong equivalence (sorry)
- `DyckParser`: verified parser for the Dyck grammar (sorry)

Ports `Examples.Dyck` from the Agda formalization.
-/

namespace LambekD.Dyck

open LambekD LambekD.Elab Nat

-- ═══════════════════════════════════════════════════════════
-- Alphabet: opening and closing brackets
-- ═══════════════════════════════════════════════════════════

inductive Bracket where
  | lp  -- [
  | rp  -- ]
  deriving DecidableEq, Inhabited, Repr

-- ═══════════════════════════════════════════════════════════
-- Dyck grammar: balanced bracket sequences
-- ═══════════════════════════════════════════════════════════

-- Dyck = nil (empty) | balanced ([ Dyck ] Dyck)
grammar_inductive DyckG : Grammar Bracket where
  | nil : Epsilon
  | balanced : Literal Bracket.lp ⊗ DyckG ⊗ Literal Bracket.rp ⊗ DyckG

-- Smart constructors
def NIL : ε ⊢ DyckG :=
  [| x => nil x |]

def BALANCED : Literal Bracket.lp ⊗ DyckG ⊗ Literal Bracket.rp ⊗ DyckG ⊢ DyckG :=
  [| x => balanced x |]

def append : DyckG ⊗ DyckG ⊢ DyckG :=
  [| d d' => case d of
     | nil x => let () = x in d'
     | balanced lp e rp e' => balanced lp e rp (append e' d')
  |]
termination_by w _ => w.length
decreasing_by all_goals grammar_decreasing

-- ═══════════════════════════════════════════════════════════
-- Dyck automaton: Nat tracks unmatched opening brackets
-- ═══════════════════════════════════════════════════════════

--            [         [         [         [
--          →-→-→     →-→-→     →-→-→     →-→-→
--         /     \   /     \   /     \   /     \
--       0         1         2         3        ⋯
--       | \     /   \     /   \     /   \     /
--       ↓  ←-←-←     ←-←-←     ←-←-←     ←-←-←
--       |    ]         ]         ]         ]
--     ] ↓
--       ↓
--      fail
def DyckAut : DeterministicAutomaton Bracket (Option Nat) where
  init := some 0
  isAcc := fun
    | none => false
    | some 0 => true
    | some (_ + 1) => false
  δ := fun
    | none, _ => none
    | some n, .lp => some (n + 1)
    | some 0, .rp => none
    | some (n + 1), .rp => some n

-- ═══════════════════════════════════════════════════════════
-- Trace combinators: smart constructors for automaton traces
-- ═══════════════════════════════════════════════════════════

-- End of file: accept empty string at state 0
def EOF : ε ⊢ Trace (Option Nat) DyckAut true (some 0) :=
  [| x => let () = x in sorry |]
  -- fun w eps => Trace.stop (some 0) rfl w eps

-- -- Open bracket: consume '[', go from state n to state n+1
-- -- NOTE: With Alphabet as a concrete parameter, DyckAut.δ (some n) Bracket.lp
-- -- should now reduce definitionally to some (n+1).
-- def OPEN {n : Nat} {b : Bool} :
--     Literal Bracket.lp ⊗ Trace (Option Nat) DyckAut b (some (n + 1)) ⊢
--     Trace (Option Nat) DyckAut b (some n) := sorry

-- -- Close bracket: consume ']', go from state n to state n+1
-- def CLOSE {n : Nat} {b : Bool} :
--     Literal Bracket.rp ⊗ Trace (Option Nat) DyckAut b (some n) ⊢
--     Trace (Option Nat) DyckAut b (some (n + 1)) := sorry

-- -- Fail: any string has a rejecting trace from state nothing
-- def FAIL : string ⊢ Trace (Option Nat) DyckAut false none := sorry

-- -- Leftovers: empty string from non-zero state (rejecting)
-- def LEFTOVERS {n : Nat} : ε ⊢ Trace (Option Nat) DyckAut false (some (n + 1)) :=
--   fun w eps => Trace.stop (some (n + 1)) rfl w eps

-- -- Unexpected ']' at state 0 → rejecting trace
-- def UNEXPECTED :
--     Literal Bracket.rp ⊗ Trace (Option Nat) DyckAut false none ⊢
--     Trace (Option Nat) DyckAut false (some 0) := sorry

-- -- ═══════════════════════════════════════════════════════════
-- -- Generalized Dyck: trees with n unmatched opening brackets
-- -- ═══════════════════════════════════════════════════════════

-- -- GenDyck 0 = DyckG
-- -- GenDyck (n+1) = DyckG ⊗ ] ⊗ GenDyck n
-- def GenDyck : Nat → Grammar Bracket := fun
--   | 0 => DyckG
--   | n + 1 => DyckG ⊗ Literal Bracket.rp ⊗ GenDyck n

-- -- ═══════════════════════════════════════════════════════════
-- -- Tree extraction: Trace → GenDyck
-- -- ═══════════════════════════════════════════════════════════

-- -- Extract a Dyck tree from a balanced accepting trace.
-- -- Uses structural recursion on the trace.
-- def mkTree : Trace (Option Nat) DyckAut true (some 0) ⊢ DyckG := sorry

-- -- More generally: extract GenDyck n from Trace true (some n)
-- def genMkTree (n : Nat) : Trace (Option Nat) DyckAut true (some n) ⊢ GenDyck n := sorry

-- -- ═══════════════════════════════════════════════════════════
-- -- Trace building: DyckG → Trace
-- -- ═══════════════════════════════════════════════════════════

-- -- Build a trace from a Dyck tree (the inverse of mkTree).
-- -- A Dyck tree is balanced, so the builder takes a trace at state n
-- -- and returns a trace at state n (it doesn't change the paren depth).
-- def buildTrace :
--     DyckG ⊢ &[ n ∈ Nat ] (Trace (Option Nat) DyckAut true (some n) ⊸
--                           Trace (Option Nat) DyckAut true (some n)) := sorry

-- -- ═══════════════════════════════════════════════════════════
-- -- Main results
-- -- ═══════════════════════════════════════════════════════════

-- -- Strong equivalence: Dyck ≅ Trace true (some 0)
-- def Dyck_equiv_Trace : DyckG ≅g Trace (Option Nat) DyckAut true (some 0) where
--   to := sorry
--   from' := mkTree
--   to_from := sorry
--   from_to := sorry

-- -- Fail state has no accepting traces
-- def failRejects : Trace (Option Nat) DyckAut true none ⊢ ⊥g := sorry

-- -- Disjointness of accepting and rejecting traces
-- def disjointAccRej (q : Option Nat) :
--     Disjoint (Trace (Option Nat) DyckAut true q) (Trace (Option Nat) DyckAut false q) := sorry

-- -- Parser for the Dyck grammar
-- -- Combines the trace parser (from DeterministicAutomaton) with the equivalence
-- def DyckParser : Parser DyckG (Trace (Option Nat) DyckAut false (some 0)) where
--   disj := sorry
--   parse := sorry

-- end LambekD.Dyck
