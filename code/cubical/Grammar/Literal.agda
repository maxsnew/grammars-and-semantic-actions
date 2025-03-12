open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal (Alphabet : hSet ℓ-zero) where

open import Grammar.Literal.Base Alphabet public
open import Grammar.Literal.Properties Alphabet public
