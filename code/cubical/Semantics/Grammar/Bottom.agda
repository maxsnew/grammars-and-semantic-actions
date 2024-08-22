open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Bottom ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Data.Empty as ⊥

open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)

private
  variable
    ℓG : Level

⊥-grammar : Grammar ℓG
⊥-grammar _ = Lift {ℓ-zero} ⊥
