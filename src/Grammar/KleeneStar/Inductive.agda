{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.KleeneStar.Inductive (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.KleeneStar.Inductive.Base Alphabet isSetAlphabet public
open import Grammar.KleeneStar.Inductive.Properties Alphabet isSetAlphabet public
