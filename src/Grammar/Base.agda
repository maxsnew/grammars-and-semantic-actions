{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import String.Base Alphabet isSetAlphabet public
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable ℓA : Level

module _ where
  module _ ℓA where
    Grammar : Type (ℓ-suc ℓA)
    Grammar = String → Type ℓA
