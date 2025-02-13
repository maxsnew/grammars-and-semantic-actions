open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Negation.Properties (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet

open import Grammar.Negation.Base Alphabet

open import Grammar.Bottom.Base Alphabet
open import Grammar.Bottom.Properties Alphabet
open import Grammar.Function Alphabet
open import Grammar.Function.Properties Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg : Level
    g : Grammar ℓg

unambiguous¬G : unambiguous (¬G g)
unambiguous¬G = unambiguous⇒ unambiguous⊥
