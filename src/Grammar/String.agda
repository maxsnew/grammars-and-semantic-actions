{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.String (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.String.Base Alphabet isSetAlphabet public
open import Grammar.String.Properties Alphabet isSetAlphabet public
open import Grammar.String.Lookahead Alphabet isSetAlphabet public
