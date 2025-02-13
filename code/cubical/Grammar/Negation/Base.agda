open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Negation.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Function Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg : Level
    g : Grammar ℓg

¬G_ : Grammar ℓg → Grammar ℓg
¬G g = g ⇒ ⊥
