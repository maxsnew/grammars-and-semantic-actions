open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Functor (Alphabet : hSet ℓ-zero) where

open import Grammar.Inductive.AsEquality.Functor Alphabet public
