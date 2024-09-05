open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sum

open import Grammar.Base Alphabet

private
  variable
    ℓG ℓG' : Level

_⊕_ : Grammar ℓG → Grammar ℓG' → Grammar (ℓ-max ℓG ℓG')
(g ⊕ g') w = g w ⊎ g' w