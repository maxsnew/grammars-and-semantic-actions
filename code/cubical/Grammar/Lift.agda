open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Lift (Alphabet : hSet ℓ-zero) where

open import Grammar.Lift.Base Alphabet public
open import Grammar.Lift.Properties Alphabet public
