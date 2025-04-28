{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.AsEquality (Alphabet : hSet ℓ-zero) where

open import Grammar.Inductive.AsEquality.HLevels Alphabet public
open import Grammar.Inductive.AsEquality.Properties Alphabet public
open import Grammar.Inductive.AsEquality.Indexed Alphabet public
