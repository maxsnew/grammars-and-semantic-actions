open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels

module Semantics.Term ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.Term.Base (Σ₀ , isSetΣ₀) public
