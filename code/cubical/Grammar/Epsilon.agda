open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Helper
open import Grammar.Base Alphabet

private
  variable
    ℓG : Level

ε : Grammar ℓ-zero
ε w = w ≡ []
