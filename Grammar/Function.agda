open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Function (Alphabet : hSet ℓ-zero) where

open import Grammar.Function.AsPrimitive.Base Alphabet public
open import Grammar.Function.AsPrimitive.Properties Alphabet public
