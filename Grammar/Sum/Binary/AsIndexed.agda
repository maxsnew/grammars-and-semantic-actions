open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Binary.AsIndexed (Alphabet : hSet ℓ-zero) where

open import Grammar.Sum.Binary.AsIndexed.Base Alphabet public
open import Grammar.Sum.Binary.AsIndexed.Properties Alphabet public
