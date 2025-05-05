{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product.Binary.AsIndexed (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Product.Binary.AsIndexed.Base Alphabet isSetAlphabet public
