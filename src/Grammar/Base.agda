open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import String.Alphabet
module Grammar.Base (Alphabet : Alphabet) where

open import String.Base Alphabet public
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable ℓA : Level

module _ where
  module _ ℓA where
    Grammar : Type (ℓ-suc ℓA)
    Grammar = String → Type ℓA
