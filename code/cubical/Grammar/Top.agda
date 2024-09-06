open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Top (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓ : Level
    g : Grammar ℓg

⊤-grammar : Grammar ℓg
⊤-grammar _ = Unit*

⊤-intro :
  g ⊢ ⊤-grammar {ℓg = ℓ}
⊤-intro _ _ = tt*
