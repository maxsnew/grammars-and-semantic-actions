{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Function (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Function.AsPrimitive.Base Alphabet isSetAlphabet public
