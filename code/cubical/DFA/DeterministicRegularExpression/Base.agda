open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module DFA.DeterministicRegularExpression.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.More
open import Cubical.Data.Bool
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Maybe as Maybe hiding (rec)

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar Alphabet
open import DFA.Base Alphabet public
open import Term Alphabet

open DeterministicAutomaton

private
  variable
    ℓ : Level

  mkFinSet :  FinSet ℓ → FinSet ℓ
  mkFinSet Q .fst = Maybe (Unit ⊎ ⟨ Q ⟩) -- inl is the initial state
  mkFinSet Q .snd = isFinSetMaybe (isFinSet⊎ (_ , isFinSetUnit) Q)

open ImplicitDeterministicAutomaton

module _
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

  ⊥Aut : ImplicitDeterministicAutomaton Empty.⊥
  ⊥Aut .acc ()
  ⊥Aut .null = false
  ⊥Aut .δ₀ _ _ = nothing

  ⊥DFA : DFAOver (mkFinSet (_ , isFinSet⊥))
  ⊥DFA = {!!}
  --   ImplicitDFA
  --     Empty.⊥
  --     Empty.rec
  --     false
  --     λ _ _ → nothing

  -- εDFA : DFAOver (mkFinSet (_ , isFinSet⊥))
  -- εDFA =
  --   ImplicitDFA
  --     Empty.⊥
  --     Empty.rec
  --     true
  --     λ _ _ → nothing

  -- literalDFA : ⟨ Alphabet ⟩ → DFAOver (mkFinSet (_ , isFinSetUnit))
  -- literalDFA c =
  --   ImplicitDFA
  --     Unit
  --     (λ _ → true)
  --     false
  --     λ {
  --       (inl _) c' →
  --         decRec
  --           (λ _ → just _)
  --           (λ _ → nothing)
  --           (DiscreteAlphabet isFinSetAlphabet c c')
  --     ; (inr q) c' → nothing
  --     }
