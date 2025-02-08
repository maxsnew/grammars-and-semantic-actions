open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Function.Properties (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.HLevels.Properties Alphabet
open import Grammar.Function.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

opaque
  unfolding _⇒_
  unambiguous⇒ : unambiguous g → unambiguous (h ⇒ g)
  unambiguous⇒ unambig-g =
    EXTERNAL.isLang→unambiguous
      (λ w → isProp→ (EXTERNAL.unambiguous→isLang unambig-g w))
