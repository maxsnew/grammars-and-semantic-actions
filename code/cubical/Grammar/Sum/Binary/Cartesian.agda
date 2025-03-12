open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Binary.Cartesian (Alphabet : hSet ℓ-zero) where

open import Grammar.Sum.Binary.Cartesian.Base Alphabet public
open import Grammar.Sum.Binary.Cartesian.Properties Alphabet public
