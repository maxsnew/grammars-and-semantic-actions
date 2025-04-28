{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Lift (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Lift.Base Alphabet isSetAlphabet public
open import Grammar.Lift.Properties Alphabet isSetAlphabet public
