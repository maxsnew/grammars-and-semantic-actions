open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.KleeneStar.Inductive (Alphabet : hSet ℓ-zero) where

open import Grammar.KleeneStar.Inductive.Base Alphabet public
open import Grammar.KleeneStar.Inductive.Properties Alphabet public
