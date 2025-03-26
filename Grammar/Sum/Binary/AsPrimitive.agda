open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Binary.AsPrimitive (Alphabet : hSet ℓ-zero) where

open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet public
open import Grammar.Sum.Binary.AsPrimitive.Properties Alphabet public
