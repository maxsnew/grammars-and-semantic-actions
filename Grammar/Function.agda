open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Function (Alphabet : hSet ℓ-zero) where

open import Grammar.Function.Cartesian.Base Alphabet public
open import Grammar.Function.Cartesian.Properties Alphabet public
