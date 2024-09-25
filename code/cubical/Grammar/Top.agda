open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Top (Alphabet : hSet ℓ-zero) where

open import Grammar.Top.Base Alphabet public
open import Grammar.Top.Properties Alphabet public
