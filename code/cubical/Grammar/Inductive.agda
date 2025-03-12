open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive (Alphabet : hSet ℓ-zero) where

open import Grammar.Inductive.HLevels Alphabet public
open import Grammar.Inductive.Indexed Alphabet public
open import Grammar.Inductive.LiftFunctor Alphabet public
open import Grammar.Inductive.Properties Alphabet public
