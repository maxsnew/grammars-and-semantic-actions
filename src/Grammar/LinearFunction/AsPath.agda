open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearFunction.AsPath (Alphabet : hSet ℓ-zero) where

open import Grammar.LinearFunction.AsPath.Base Alphabet public
open import Grammar.LinearFunction.AsPath.Properties Alphabet public
