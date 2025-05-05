{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal.AsEquality (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Literal.AsEquality.Base Alphabet isSetAlphabet public
open import Grammar.Literal.AsEquality.Properties Alphabet isSetAlphabet public
