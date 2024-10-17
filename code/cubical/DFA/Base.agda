open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module DFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet

open import Grammar Alphabet
open import Automaton.Deterministic Alphabet public

private
  variable
    ℓD : Level

open DeterministicAutomaton 

DFA : FinSet ℓD → Type (ℓ-suc ℓD)
DFA Q = DeterministicAutomaton ⟨ Q ⟩
