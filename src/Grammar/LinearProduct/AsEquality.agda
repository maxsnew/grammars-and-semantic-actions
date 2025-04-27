{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.AsEquality (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.LinearProduct.AsEquality.Base Alphabet isSetAlphabet public
open import Grammar.LinearProduct.AsEquality.Properties Alphabet isSetAlphabet public
