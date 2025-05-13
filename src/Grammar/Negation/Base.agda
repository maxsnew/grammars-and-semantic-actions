{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Negation.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Bottom.Base Alphabet isSetAlphabet
open import Grammar.Function.AsPrimitive.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA : Level
    A : Grammar ℓA

¬G_ : Grammar ℓA → Grammar ℓA
¬G_ {ℓA = ℓA} A = A ⇒ (⊥ {ℓA})
infix 30 ¬G_
