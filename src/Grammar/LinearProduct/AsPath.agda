open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.LinearProduct.AsPath (Alphabet : hSet ℓ-zero) where

open import Grammar.LinearProduct.AsPath.Base Alphabet public
open import Grammar.LinearProduct.AsPath.Properties Alphabet public
