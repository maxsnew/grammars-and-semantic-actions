open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearFunction (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Grammar.Base Alphabet

private
  variable
    ℓG ℓG' : Level

_-⊗_ : Grammar ℓG → Grammar ℓG' → Grammar (ℓ-max ℓG ℓG')
(g -⊗ g') w = ∀ (w' : String) → g w' → g' (w' ++ w)

_⊗-_ : Grammar ℓG → Grammar ℓG' → Grammar (ℓ-max ℓG ℓG')
(g ⊗- g') w = ∀ (w' : String) → g' w' → g (w ++ w')
