{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.LinearProduct.AsPath (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.LinearProduct.AsPath.Base Alphabet isSetAlphabet public
open import Grammar.LinearProduct.AsPath.Properties Alphabet isSetAlphabet public
