open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Empty ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Data.List

open import Semantics.Helper
open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)

private
  variable
    ℓG : Level

ε-grammar : Grammar ℓ-zero
ε-grammar w = w ≡ []
