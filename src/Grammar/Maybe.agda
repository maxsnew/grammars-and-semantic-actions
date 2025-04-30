{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Maybe (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Maybe.Base Alphabet isSetAlphabet public
