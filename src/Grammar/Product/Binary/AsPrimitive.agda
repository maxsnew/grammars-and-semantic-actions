{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product.Binary.AsPrimitive (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet public
open import Grammar.Product.Binary.AsPrimitive.Properties Alphabet isSetAlphabet public
