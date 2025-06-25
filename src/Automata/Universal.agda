{- The universal automaton for Grammars (of level ℓ) is an automaton whose states are grammars and whose transition function is the derivative -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module Automata.Universal (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.List hiding (init ; rec ; map)
import Cubical.Data.Equality as Eq

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet

private
  variable ℓN ℓN' ℓP : Level

module _ {ℓ : Level} where
  data UniversalTag (A : Grammar ℓ) : Type (ℓ-suc ℓ) where
    stop : ↑ A → UniversalTag A
    step : ⟨ Alphabet ⟩ → UniversalTag A
  UniversalF : (Grammar ℓ) → Functor (Grammar ℓ)
  UniversalF A = ⊕e (UniversalTag A) (λ where
    (stop x) → k ε*
    (step c) → k (literal* c) ⊗e Var (A ⟜ literal c))

  πAlg : Algebra UniversalF λ A → A
  πAlg A = ⊕ᴰ-elim (λ where
    (stop a) → (ε-elim a ∘g lowerG) ∘g lowerG
    (step x) → ⟜-app ∘g (lowerG ∘g lowerG) ,⊗ lowerG)

  πU : ∀ {A} → μ UniversalF A ⊢ A
  πU = rec UniversalF πAlg _

  -- TODO: πU is an iso. Not sure if this is provable from the axioms we already have, or if it's useful for anything yet.
