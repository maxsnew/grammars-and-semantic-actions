{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearFunction.AsEquality (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.LinearFunction.AsEquality.Base Alphabet isSetAlphabet public
open import Grammar.LinearFunction.AsEquality.Properties Alphabet isSetAlphabet public
