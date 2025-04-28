{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Term.Base Alphabet isSetAlphabet public
open import Term.Nullary Alphabet isSetAlphabet public
