{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Literal.Base Alphabet isSetAlphabet public
open import Grammar.Literal.Properties Alphabet isSetAlphabet public
