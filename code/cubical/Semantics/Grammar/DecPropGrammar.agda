open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.DecPropGrammar ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Semantics.Helper
open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Top (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Bottom (Σ₀ , isSetΣ₀)

private
  variable
    ℓG ℓS : Level

DecProp-grammar' :
  DecProp ℓS → Grammar (ℓ-max ℓS ℓG)
DecProp-grammar' d =
  decRec
    (λ _ → ⊤-grammar)
    (λ _ → ⊥*-grammar) (d .snd)
