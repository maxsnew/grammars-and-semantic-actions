{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal.AsPath (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Literal.AsPath.Base Alphabet isSetAlphabet public
open import Grammar.Literal.AsPath.Properties Alphabet isSetAlphabet public
