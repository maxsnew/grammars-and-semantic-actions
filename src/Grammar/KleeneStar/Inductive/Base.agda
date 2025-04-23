open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.KleeneStar.Inductive.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.KleeneStar.Inductive.AsEquality.Base Alphabet public
