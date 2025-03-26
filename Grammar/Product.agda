open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product (Alphabet : hSet ℓ-zero) where

open import Grammar.Product.Base Alphabet public
open import Grammar.Product.Properties Alphabet public
