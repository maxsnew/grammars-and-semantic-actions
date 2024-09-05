open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Equivalence (Alphabet : hSet ℓ-zero) where

open import Grammar.Equivalence.Base Alphabet public
open import Grammar.Equivalence.Combinators Alphabet public
