open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Epsilon.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
open import Grammar.Properties Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.HLevels.Properties Alphabet
open import Term Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

unambiguousε : unambiguous ε
unambiguousε = summand-L-is-unambig (unambiguous≅ unroll-string≅ unambiguous-string)

unambiguousε* : ∀ {ℓ} → unambiguous (ε* {ℓ})
unambiguousε* {ℓ = ℓ} = unambiguous≅ (LiftG≅ ℓ ε) unambiguousε
