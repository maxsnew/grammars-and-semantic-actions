{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Bottom.Base Alphabet isSetAlphabet public
open import Grammar.Bottom.Properties Alphabet isSetAlphabet public
