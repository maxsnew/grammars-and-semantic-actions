{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom (Alphabet : hSet ℓ-zero) where

open import Grammar.Bottom.Base Alphabet public
open import Grammar.Bottom.Properties Alphabet public
