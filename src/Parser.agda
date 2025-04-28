{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Parser (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Parser.Base Alphabet isSetAlphabet public
