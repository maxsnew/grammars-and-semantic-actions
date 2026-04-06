import LambekD.Automata.DFA.Base
import LambekD.Grammar.String.Base
import Mathlib.Computability.DFA
import Mathlib.Computability.Language

/-!
# Bridge between LambekD automata and Mathlib's computability library

Connects LambekD's grammar-indexed `DeterministicAutomaton` / `DFA` / `Trace` to
Mathlib's `DFA` and `Language.IsRegular`.

## Main definitions

- `Grammar.toLang`: convert a grammar `String → Type` to a Mathlib language `Set (List Alphabet)`
- `DeterministicAutomaton.toMathlib`: convert a LambekD deterministic automaton to a Mathlib DFA
- `DeterministicAutomaton.runFrom`: evaluate the automaton as `List.foldl δ q w`

## Main theorems

- `DeterministicAutomaton.eval_eq`: `toMathlib.evalFrom` agrees with `runFrom`
- `Trace.finalState_eq`: a trace on `w` from `q` implies the final state satisfies the `b` flag
- `DeterministicAutomaton.toLang_trace`: the grammar `Trace Q da true da.init` equals
  `da.toMathlib.accepts` as a language
- `DFA.isRegular`: languages recognized by LambekD DFAs are regular
-/

namespace LambekD

open LambekD Computability

universe uAlph

variable {Alphabet : Type uAlph}

-- ═══════════════════════════════════════════════════════════
-- Grammar → Language conversion
-- ═══════════════════════════════════════════════════════════

/-- Convert a grammar (denotational: `String → Type`) to a Mathlib language (`Set (List Alphabet)`).
    A string is in the language iff the grammar has at least one parse tree for it. -/
def Grammar.toLang (A : Grammar Alphabet) : Language Alphabet :=
  {w | Nonempty (A w)}

theorem Grammar.mem_toLang {A : Grammar Alphabet} {w : LambekD.String Alphabet} :
    w ∈ A.toLang ↔ Nonempty (A w) :=
  Iff.rfl

-- ═══════════════════════════════════════════════════════════
-- DeterministicAutomaton → Mathlib DFA
-- ═══════════════════════════════════════════════════════════

/-- Convert a LambekD `DeterministicAutomaton` to a Mathlib `DFA`.
    The transition function and initial state transfer directly;
    the Boolean acceptance predicate becomes a `Set`. -/
def DeterministicAutomaton.toMathlib {Q : Type} (da : DeterministicAutomaton Alphabet Q) :
    _root_.DFA Alphabet Q where
  step := da.δ
  start := da.init
  accept := {q | da.isAcc q = true}

/-- Evaluate the automaton from state `q` on string `w` by left-folding the transition function. -/
def DeterministicAutomaton.runFrom {Q : Type} (da : DeterministicAutomaton Alphabet Q) (q : Q)
    (w : LambekD.String Alphabet) : Q :=
  List.foldl da.δ q w

/-- Evaluate the automaton from the initial state. -/
def DeterministicAutomaton.run {Q : Type} (da : DeterministicAutomaton Alphabet Q)
    (w : LambekD.String Alphabet) : Q :=
  da.runFrom da.init w

-- ═══════════════════════════════════════════════════════════
-- Evaluation agreement
-- ═══════════════════════════════════════════════════════════

/-- `toMathlib.evalFrom` is definitionally equal to `runFrom`. -/
theorem DeterministicAutomaton.eval_eq {Q : Type} (da : DeterministicAutomaton Alphabet Q) (q : Q)
    (w : LambekD.String Alphabet) : da.toMathlib.evalFrom q w = da.runFrom q w :=
  rfl

/-- `toMathlib.eval` is definitionally equal to `run`. -/
theorem DeterministicAutomaton.eval_eq' {Q : Type} (da : DeterministicAutomaton Alphabet Q)
    (w : LambekD.String Alphabet) : da.toMathlib.eval w = da.run w :=
  rfl

-- ═══════════════════════════════════════════════════════════
-- Trace ↔ acceptance correspondence
-- ═══════════════════════════════════════════════════════════

/-- A `Trace Q da b q` on string `w` witnesses that `List.foldl da.δ q w` reaches a state
    whose acceptance flag equals `b`. This is the core semantic content of the trace grammar. -/
theorem Trace.finalState_eq {Q : Type} {da : DeterministicAutomaton Alphabet Q} {b : Bool} {q : Q}
    {w : LambekD.String Alphabet} (t : Trace Q da b q w) : da.isAcc (da.runFrom q w) = b := by
  induction t with
  | stop q h _ eps =>
    obtain ⟨⟨rfl⟩⟩ := eps
    exact h.symm
  | step q c w' s lit trace ih =>
    obtain ⟨⟨hlit⟩⟩ := lit
    -- hlit : s.left = [c], s.eq : s.left ++ s.right = w'
    -- ih : da.isAcc (da.runFrom (da.δ q c) s.right) = b
    have hw : w' = [c] ++ s.right := by
      have h := s.eq.symm; rw [hlit] at h; exact h
    simp only [DeterministicAutomaton.runFrom, hw, List.foldl_append, List.foldl_cons,
               List.foldl_nil]
    exact ih

/-- The `parse` function computes the correct acceptance flag: the `b` component
    of `da.parse w s q` equals `da.isAcc (da.runFrom q w)`. -/
theorem DeterministicAutomaton.parse_acc_eq {Q : Type} (da : DeterministicAutomaton Alphabet Q)
    (q : Q) (w : LambekD.String Alphabet) (s : string w) :
    (da.parse w s q).1 = da.isAcc (da.runFrom q w) :=
  (da.parse w s q).2.finalState_eq.symm

-- ═══════════════════════════════════════════════════════════
-- Language correspondence
-- ═══════════════════════════════════════════════════════════

/-- The language of the accepting trace grammar from the initial state equals
    the Mathlib DFA's accepted language. -/
theorem DeterministicAutomaton.toLang_trace {Q : Type} (da : DeterministicAutomaton Alphabet Q) :
    Grammar.toLang (Trace Q da true da.init) = da.toMathlib.accepts := by
  ext w
  constructor
  · -- Forward: a trace witnesses acceptance
    rintro ⟨t⟩
    -- t : Trace Q da true da.init w
    -- Goal: w ∈ da.toMathlib.accepts
    -- Unfolds to: da.isAcc (List.foldl da.δ da.init w) = true
    exact t.finalState_eq
  · -- Backward: if the automaton accepts, parse produces an accepting trace
    intro hacc
    -- hacc : w ∈ da.toMathlib.accepts
    -- Unfolds to: da.isAcc (List.foldl da.δ da.init w) = true
    let p := da.parse w (mkString w) da.init
    -- p.1 : Bool, p.2 : Trace Q da p.1 da.init w
    have hb : p.1 = true := by
      rw [← p.2.finalState_eq]
      exact hacc
    exact ⟨hb ▸ p.2⟩

-- ═══════════════════════════════════════════════════════════
-- Regularity
-- ═══════════════════════════════════════════════════════════

/-- Any language recognized by a LambekD DFA (via the accepting trace grammar from the
    initial state) is regular in the sense of Mathlib's `Language.IsRegular`. -/
theorem DFA.isRegular (dfa : LambekD.DFA Alphabet) :
    (Grammar.toLang (Trace dfa.Q dfa.da true dfa.da.init)).IsRegular :=
  ⟨dfa.Q, dfa.fintype, dfa.da.toMathlib, dfa.da.toLang_trace.symm⟩

end LambekD
