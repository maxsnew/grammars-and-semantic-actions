open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.External.HLevels (Alphabet : hSet ℓ-zero) where

open import Grammar.External.HLevels.MonoInjective Alphabet public
open import Grammar.External.HLevels.Properties Alphabet public
