open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.AsEquality (Alphabet : hSet ℓ-zero) where

open import Grammar.LinearProduct.AsEquality.Base Alphabet public
open import Grammar.LinearProduct.AsEquality.Properties Alphabet public
