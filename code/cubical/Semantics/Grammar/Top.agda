open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Top ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Data.Unit

open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)

private
  variable
    ℓG : Level

⊤-grammar : Grammar ℓG
⊤-grammar _ = Unit*
