import LambekD.Automata.Deterministic
import LambekD.Grammar.Properties.Base
import LambekD.Parser.Base

/-!
# Binary operation expression grammar and LL(1) parser

Defines the grammar of arithmetic expressions with one binary operation (+),
natural number constants, and parentheses. Constructs an LL(1) lookahead
automaton and proves (weakly) that it accepts exactly the expression grammar.

Key components:
- `Tok`: token type (parens, +, num n)
- `EXP`, `ATOM`: the LL(1) grammar nonterminals
- `Automaton`: LL(1) lookahead automaton with Opening/Closing/Adding states
- `TraceParser`: parser for automaton traces
- `AccTrace_weakEquiv_EXP`: weak equivalence (sorry)
- `EXPParser`: verified parser for expressions (sorry)

Ports `Examples.BinOp` from the Agda formalization.
-/

namespace LambekD.BinOp

open LambekD LambekD.Elab Nat

-- ═══════════════════════════════════════════════════════════
-- Alphabet: tokens for binary operation expressions
-- ═══════════════════════════════════════════════════════════

inductive Tok : Type where
  | lparen : Tok     -- [
  | rparen : Tok     -- ]
  | plus : Tok       -- +
  | num : Nat → Tok    -- constants
  deriving DecidableEq, Inhabited, Repr

-- ═══════════════════════════════════════════════════════════
-- The LL(1) grammar: nonterminals EXP and ATOM
-- ═══════════════════════════════════════════════════════════

-- The grammar is:
--   E → A | A + E
--   A → num n | [ E ]
--
-- Mutual recursion is encoded via a single indexed grammar_inductive
-- over a nonterminal tag, mirroring the Agda μ-type approach.

-- anyNum: the grammar that accepts any single number token
def anyNum : Grammar Tok := ⊕[n ∈ Nat] lit(Tok.num n)

-- Nonterminal tag for mutual recursion
inductive Nonterminal where
  | Exp | Atom
  deriving DecidableEq

-- Single indexed inductive encoding both EXP and ATOM
grammar_inductive BinOpG : Nonterminal → Grammar Tok where
  | done : ↑(BinOpG Nonterminal.Atom ⊸ BinOpG Nonterminal.Exp)
  | add : ↑(BinOpG Nonterminal.Atom ⊗ Literal Tok.plus ⊗ BinOpG Nonterminal.Exp ⊸ BinOpG Nonterminal.Exp)
  | num : ↑(anyNum ⊸ BinOpG Nonterminal.Atom)
  | parens : ↑(Literal Tok.lparen ⊗ BinOpG Nonterminal.Exp ⊗ Literal Tok.rparen ⊸ BinOpG Nonterminal.Atom)

-- Abbreviations for the two nonterminals
abbrev EXP : Grammar Tok := BinOpG Nonterminal.Exp
abbrev ATOM : Grammar Tok := BinOpG Nonterminal.Atom

-- ═══════════════════════════════════════════════════════════
-- LL(1) Lookahead Automaton
-- ═══════════════════════════════════════════════════════════

-- The automaton has three states per paren-depth:
-- Opening: expecting an atom (number or '(')
-- Closing: expecting ')' to close a paren group
-- Adding: expecting '+' to continue, or end-of-input
inductive AutomatonState where
  | Opening | Closing | Adding
  deriving DecidableEq, Repr

-- The full automaton state is (Nat × AutomatonState) with Option for failure.
-- We use Option (Nat × AutomatonState) but simplify by inlining failure into
-- the transition function.

-- Map peeked token to the next automaton state category
def tokToState : Option Tok → AutomatonState
  | some Tok.rparen => .Closing
  | none => .Adding
  | some Tok.lparen => .Adding
  | some Tok.plus => .Adding
  | some (Tok.num _) => .Adding

-- The deterministic automaton over (Nat × AutomatonState)
-- We use a product state to track both paren depth and parser phase
-- The acceptance predicate: accept only at (0, Adding) — we've consumed
-- all tokens and all parens are matched.
-- NOTE: The full Agda version has a more refined trace type with
-- acceptance/rejection tracking. Here we give a simplified version.
def BinOpAut : DeterministicAutomaton Tok (Bool × Nat × AutomatonState) where
  init := (true, 0, .Opening)
  isAcc := fun
    | (true, 0, .Adding) => true
    | _ => false
  δ := fun (q : Bool × Nat × AutomatonState) (c : Tok) => match q, c with
    | (true, n, .Opening), Tok.lparen => (true, n + 1, .Opening)
    | (true, n, .Opening), Tok.num _ => (true, n, .Adding)
    | (true, _, .Opening), _ => (false, 0, .Opening)
    | (true, 0, .Closing), Tok.rparen => (false, 0, .Closing)
    | (true, n + 1, .Closing), Tok.rparen => (true, n, .Adding)
    | (true, _, .Closing), _ => (false, 0, .Closing)
    | (true, n, .Adding), Tok.plus => (true, n, .Opening)
    | (true, _, .Adding), _ => (false, 0, .Adding)
    | (false, _, _), _ => (false, 0, .Opening)

-- ═══════════════════════════════════════════════════════════
-- Main results (stated with sorry)
-- ═══════════════════════════════════════════════════════════

-- Soundness: from every accepting trace we can extract an EXP parse
def buildExp :
    Trace (Bool × Nat × AutomatonState) BinOpAut true BinOpAut.init ⊢ EXP := sorry

-- Completeness: from every EXP parse we can build an accepting trace
def mkTrace :
    EXP ⊢ Trace (Bool × Nat × AutomatonState) BinOpAut true BinOpAut.init := sorry

-- Weak equivalence between accepting traces and EXP
def AccTrace_weakEquiv_EXP :
    Trace (Bool × Nat × AutomatonState) BinOpAut true BinOpAut.init ≈g EXP where
  to := buildExp
  from' := mkTrace

-- Parser for EXP
def EXPParser : Parser EXP (Trace (Bool × Nat × AutomatonState) BinOpAut false BinOpAut.init) where
  disj := sorry
  parse := sorry

end LambekD.BinOp
