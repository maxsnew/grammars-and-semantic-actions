open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent (Alphabet : hSet ℓ-zero) where
open import Grammar.Dependent.Base Alphabet public
open import Grammar.Dependent.Properties Alphabet public
