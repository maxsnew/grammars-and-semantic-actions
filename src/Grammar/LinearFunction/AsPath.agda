{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearFunction.AsPath (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.LinearFunction.AsPath.Base Alphabet isSetAlphabet public
open import Grammar.LinearFunction.AsPath.Properties Alphabet isSetAlphabet public
