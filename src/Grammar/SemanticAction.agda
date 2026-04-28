open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.SemanticAction (Alphabet : hSet ℓ-zero) where

open import Grammar.SemanticAction.Base Alphabet public
open import Grammar.SemanticAction.Monadic Alphabet public
