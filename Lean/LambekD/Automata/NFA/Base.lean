import LambekD.Elab
import LambekD.Grammar.Equivalence

/-!
# Non-deterministic finite automata

NFA record with states, labeled transitions, and ε-transitions.
The `AccTrace` grammar tracks accepting runs of the NFA as
indexed parse trees.

Ports `Automata.NFA.Base` (Accepting module) from the Agda formalization.
-/

namespace LambekD

open LambekD LambekD.Elab

universe uAlph

variable {Alphabet : Type uAlph}

structure NFA (Alphabet : Type uAlph) where
  Q : Type
  init : Q
  isAcc : Q → Bool
  Transition : Type
  src : Transition → Q
  dst : Transition → Q
  label : Transition → Alphabet
  ETransition : Type
  εSrc : ETransition → Q
  εDst : ETransition → Q

-- Accepting trace: indexed grammar recording the NFA's accepting run.
-- stop: accept empty string at accepting state
-- step: consume a character via a labeled transition
-- stepε: follow an ε-transition without consuming input
grammar_inductive AccTrace (nfa : NFA Alphabet) : nfa.Q → Grammar Alphabet where
  | stop : ↑(&[ q ∈ nfa.Q ] &[ h ∈ true = nfa.isAcc q ] AccTrace nfa q)
  | step : ↑(&[ t ∈ nfa.Transition ] lit(nfa.label t) ⊸ AccTrace nfa (nfa.dst t) ⊸ AccTrace nfa (nfa.src t))
  | stepε : ↑(&[ t ∈ nfa.ETransition ] AccTrace nfa (nfa.εDst t) ⊸ AccTrace nfa (nfa.εSrc t))

namespace NFA

variable {nfa : NFA Alphabet}

@[reducible] def Parse (nfa : NFA Alphabet) : Grammar Alphabet := AccTrace nfa nfa.init

-- Smart constructors matching the Agda API
def STOP {q : nfa.Q} (h : true = nfa.isAcc q) : ε ⊢ AccTrace nfa q :=
  fun w eps => AccTrace.stop q h w eps

def STEP (t : nfa.Transition) : lit(nfa.label t) ⊗ AccTrace nfa (nfa.dst t) ⊢ AccTrace nfa (nfa.src t) :=
  fun w tensor => AccTrace.step t w tensor.split tensor.fst tensor.snd

def STEPε (t : nfa.ETransition) : AccTrace nfa (nfa.εDst t) ⊢ AccTrace nfa (nfa.εSrc t) :=
  fun w trace => AccTrace.stepε t w trace

end NFA

end LambekD
