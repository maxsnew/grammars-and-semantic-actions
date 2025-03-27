open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Function.AsPrimitive.Properties (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.External.HLevels.Properties Alphabet
open import Grammar.Function.AsPrimitive.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

opaque
  unfolding _⇒_
  unambiguous⇒ : unambiguous A → unambiguous (B ⇒ A)
  unambiguous⇒ unambig-A =
    isLang→unambiguous (λ w → isProp→ (unambiguous→isLang unambig-A w))
