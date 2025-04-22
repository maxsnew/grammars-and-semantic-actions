open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Indexed (Alphabet : hSet ℓ-zero) where

open import Grammar.Inductive.AsEquality.Indexed Alphabet public
