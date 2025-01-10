open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module DFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.Bool

open import Grammar Alphabet
open import Automaton.Deterministic Alphabet public

private
  variable
    ℓD : Level

open DeterministicAutomaton

DFAOver : FinSet ℓD → Type (ℓ-suc ℓD)
DFAOver Q = DeterministicAutomaton ⟨ Q ⟩

DFA : Type (ℓ-suc ℓD)
DFA {ℓD = ℓD} = Σ[ A ∈ FinSet ℓD ] DFAOver A
