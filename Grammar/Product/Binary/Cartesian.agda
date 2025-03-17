open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product.Binary.Cartesian (Alphabet : hSet ℓ-zero) where

open import Grammar.Product.Binary.Cartesian.Base Alphabet public
open import Grammar.Product.Binary.Cartesian.Properties Alphabet public
