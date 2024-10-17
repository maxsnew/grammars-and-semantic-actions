open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.KleeneStar (Alphabet : hSet ℓ-zero) where

open import Grammar.KleeneStar.Inductive Alphabet public
