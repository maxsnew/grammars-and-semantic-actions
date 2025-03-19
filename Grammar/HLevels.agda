open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.HLevels (Alphabet : hSet ℓ-zero) where

open import Grammar.HLevels.Base Alphabet public
open import Grammar.HLevels.Properties Alphabet public
-- open import Grammar.HLevels.MonoInjective Alphabet public
