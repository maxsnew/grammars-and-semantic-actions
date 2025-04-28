{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Inductive.HLevels Alphabet isSetAlphabet public
open import Grammar.Inductive.Indexed Alphabet isSetAlphabet public
open import Grammar.Inductive.Properties Alphabet isSetAlphabet public
