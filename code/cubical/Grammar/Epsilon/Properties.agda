open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Epsilon.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.HLevels.Properties Alphabet
open import Term Alphabet
open import Helper

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

unambiguousε : unambiguous ε
unambiguousε = ans
  where
  opaque
    unfolding ε
    ans : unambiguous ε
    ans = EXTERNAL.isLang→unambiguous isLangε

unambiguousε* : ∀ {ℓ} → unambiguous (ε* {ℓ})
unambiguousε* {ℓ = ℓ} = ans
  where
  opaque
    unfolding ε
    ans : unambiguous (ε* {ℓ})
    ans = EXTERNAL.isLang→unambiguous
      λ w → isPropLift (isLangε w)
