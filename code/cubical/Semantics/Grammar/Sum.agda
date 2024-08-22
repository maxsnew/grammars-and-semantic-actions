open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Sum ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Data.Sum

open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)

private
  variable
    ℓG ℓG' : Level

_⊕_ : Grammar ℓG → Grammar ℓG' → Grammar (ℓ-max ℓG ℓG')
(g ⊕ g') w = g w ⊎ g' w
