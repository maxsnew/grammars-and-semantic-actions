open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.DFA ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.DFA.Base (Σ₀ , isSetΣ₀) public
open import Semantics.DFA.Decider (Σ₀ , isSetΣ₀) public
