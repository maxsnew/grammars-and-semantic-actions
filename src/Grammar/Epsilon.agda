{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Epsilon.Base Alphabet isSetAlphabet public
open import Grammar.Epsilon.Properties Alphabet isSetAlphabet public
