{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Product.Base Alphabet isSetAlphabet public
open import Grammar.Product.Properties Alphabet isSetAlphabet public
