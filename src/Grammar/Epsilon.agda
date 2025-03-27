open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon (Alphabet : hSet ℓ-zero) where

open import Grammar.Epsilon.Base Alphabet public
open import Grammar.Epsilon.Properties Alphabet public
