open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Epsilon.AsEquality.Base Alphabet public
open import Grammar.Epsilon.AsEquality.Properties Alphabet public
