import LambekD.Automata.Deterministic
import Mathlib.Data.Fintype.Basic

/-!
# Deterministic finite automata

A DFA is a `DeterministicAutomaton` whose state type is finite
(has `Fintype` and `DecidableEq` instances).

Ports `Automata.DFA.Base` from the Agda formalization.
-/

namespace LambekD

open LambekD

universe uAlph

variable {Alphabet : Type uAlph}

structure DFA (Alphabet : Type uAlph) where
  Q : Type
  [fintype : Fintype Q]
  [deceq : DecidableEq Q]
  da : DeterministicAutomaton Alphabet Q

attribute [instance] DFA.fintype DFA.deceq

end LambekD
