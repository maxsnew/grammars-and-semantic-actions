open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Reify.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.String.Base Alphabet

private
  variable ℓA ℓB : Level

module _ (P : String → Type ℓA) where
  Reify : Grammar ℓA
  Reify = ⊕[ w ∈ String ] ⊕[ x ∈ P w ] ⌈ w ⌉

