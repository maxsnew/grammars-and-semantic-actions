open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearFunction.AsEquality (Alphabet : hSet ℓ-zero) where

open import Grammar.LinearFunction.AsEquality.Base Alphabet public
open import Grammar.LinearFunction.AsEquality.Properties Alphabet public
