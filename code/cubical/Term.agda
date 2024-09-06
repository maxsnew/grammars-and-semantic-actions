open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term (Alphabet : hSet ℓ-zero) where

open import Term.Base Alphabet public
open import Term.Functoriality Alphabet public
