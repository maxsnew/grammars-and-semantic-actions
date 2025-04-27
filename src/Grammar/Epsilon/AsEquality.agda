{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.AsEquality (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Epsilon.AsEquality.Base Alphabet isSetAlphabet public
open import Grammar.Epsilon.AsEquality.Properties Alphabet isSetAlphabet public
