import LambekD.Elab
import LambekD.Grammar.KleeneStar.Base
import LambekD.Grammar.String.Base
import LambekD.Grammar.String.Terminal
import LambekD.Grammar.Equivalence
import LambekD.Grammar.Properties.Base

/-!
# Deterministic automata and trace grammars

A `DeterministicAutomaton` has states `Q`, an initial state, an acceptance
predicate, and a transition function. The `Trace` indexed grammar tracks
the automaton's execution: each trace is a parse tree witnessing the
automaton's run on a string from a given state.

Key results:
- `parse`: every string has a trace from every state
- `print`: every trace yields a string
- `parseInit`: parse from the initial state

Ports `Automata.Deterministic` from the Agda formalization.
-/

namespace LambekD

open LambekD LambekD.Elab

universe uAlph

variable {Alphabet : Type uAlph}

structure DeterministicAutomaton (Alphabet : Type uAlph) (Q : Type) where
  init : Q
  isAcc : Q → Bool
  δ : Q → Alphabet → Q

-- Trace: indexed inductive tracking state and acceptance.
-- `Trace Q da b q` is a grammar indexed by state `q : Q`, parameterized by
-- acceptance flag `b : Bool`. It records the automaton's run.
--
-- stop: at state q where b = isAcc q, accept the empty string
-- step: at state q, consume character c, continue from state δ q c
grammar_inductive Trace (Q : Type) (da : DeterministicAutomaton Alphabet Q) (b : Bool) : Q → Grammar Alphabet where
  | stop : ↑(&[ q ∈ Q ] &[ h ∈ b = da.isAcc q ] Trace Q da b q)
  | step : ↑(&[ q ∈ Q ] &[ c ∈ Alphabet ] lit(c) ⊸ Trace Q da b (da.δ q c) ⊸ Trace Q da b q)

namespace DeterministicAutomaton

variable {Q : Type} (da : DeterministicAutomaton Alphabet Q)

-- Parse: fold over string = char * to build traces for all states simultaneously.
-- For each state q, we track ⊕[b] Trace Q da b q — the acceptance flag is
-- determined by the automaton's run.
def parse : string ⊢ &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace Q da b q) :=
  foldStarR nilCase consCase
where
  nilCase : ε ⊢ &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace Q da b q) :=
    fun w eps q => ⟨da.isAcc q, Trace.stop q rfl w eps⟩
  consCase : char ⊗ (&[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace Q da b q)) ⊢
             &[ q ∈ Q ] (⊕[ b ∈ Bool ] Trace Q da b q) :=
    fun w t q =>
      let ⟨c, litParse⟩ := t.fst
      let ⟨b, traceParse⟩ := t.snd (da.δ q c)
      ⟨b, Trace.step q c w t.split litParse traceParse⟩

-- Parse from the initial state.
def parseInit : string ⊢ ⊕[ b ∈ Bool ] Trace Q da b da.init :=
  fun w s => da.parse w s da.init

-- Print: convert a trace back to a string by structural recursion.
def print (b : Bool) (q : Q) : Trace Q da b q ⊢ string :=
  fun w t => go w t
where
  go : ∀ {q : Q} (w : LambekD.String Alphabet), Trace Q da b q w → string w
  | _, _, .stop _ _ _ eps => KleeneStar.nil _ eps
  | _, _, .step _ c _ s lit trace =>
    KleeneStar.cons _ s ⟨c, lit⟩ (go _ trace)

-- Strong equivalence: ⊕[b] Trace b q ≅ string.
-- The forward direction prints, the inverse parses.
-- sec uses unambiguity of string; ret requires an inductive argument.
def Trace_equiv_string (q : Q) : (⊕[ b ∈ Bool ] Trace Q da b q) ≅g string where
  to := fun w ⟨b, trace⟩ => da.print b q w trace
  from' := fun w s => da.parse w s q
  to_from := sorry
  from_to := sorry

end DeterministicAutomaton

end LambekD
