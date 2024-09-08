open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Empty (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Helper
open import Grammar.Base Alphabet

private
  variable
    ℓG : Level

ε-grammar : Grammar ℓ-zero
ε-grammar w = w ≡ []

-- TODO: actually rename
ε = ε-grammar
