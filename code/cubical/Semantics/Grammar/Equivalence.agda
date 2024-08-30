open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Equivalence ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.Grammar.Equivalence.Base (Σ₀ , isSetΣ₀) public
open import Semantics.Grammar.Equivalence.Combinators (Σ₀ , isSetΣ₀) public
