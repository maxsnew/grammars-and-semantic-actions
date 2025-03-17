open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct (Alphabet : hSet ℓ-zero) where

open import Grammar.LinearProduct.Base Alphabet public
open import Grammar.LinearProduct.SplittingTrichotomy Alphabet public
