open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product.Binary.AsPrimitive (Alphabet : hSet ℓ-zero) where

open import Grammar.Product.Binary.AsPrimitive.Base Alphabet public
open import Grammar.Product.Binary.AsPrimitive.Properties Alphabet public
