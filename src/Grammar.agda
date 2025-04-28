{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Core Alphabet isSetAlphabet public
open import Grammar.BinopsAsPrimitive Alphabet isSetAlphabet public
