{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Binary.AsIndexed (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Sum.Binary.AsIndexed.Base Alphabet isSetAlphabet public
open import Grammar.Sum.Binary.AsIndexed.Properties Alphabet isSetAlphabet public
