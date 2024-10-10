open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet

open import Grammar Alphabet
open import Automaton.Deterministic Alphabet

private
  variable ℓD : Level

open DeterministicAutomaton

DFA : Type (ℓ-suc ℓD)
DFA {ℓD = ℓD} = Σ[ D ∈ DeterministicAutomaton ℓD ] isFinSet (D .Q)

