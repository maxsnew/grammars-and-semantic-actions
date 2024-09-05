open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Top (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit

open import Grammar.Base Alphabet

private
  variable
    ℓG : Level

⊤-grammar : Grammar ℓG
⊤-grammar _ = Unit*
