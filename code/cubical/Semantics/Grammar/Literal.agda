open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Literal ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Data.List

open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)

private
  variable
    ℓG : Level

literal : Σ₀ → Grammar ℓ-zero
literal c w = w ≡ [ c ]
