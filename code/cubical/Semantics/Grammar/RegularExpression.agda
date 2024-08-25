open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.RegularExpression ((Σ₀ , isSetΣ₀) : hSet ℓ-zero)where

open import Semantics.Helper
open import Semantics.Grammar (Σ₀ , isSetΣ₀)

private
  variable ℓG ℓG' : Level


module _ where
  data RegularExpression  : Type ℓ-zero where
    ε-Reg : RegularExpression
    ⊥-Reg : RegularExpression
    _⊗Reg_ : RegularExpression →
      RegularExpression → RegularExpression
    literalReg : Σ₀ → RegularExpression
    _⊕Reg_ : RegularExpression → RegularExpression → RegularExpression
    KL*Reg : RegularExpression → RegularExpression

  RegularExpression→Grammar : RegularExpression → Grammar ℓ-zero
  RegularExpression→Grammar  ε-Reg = ε-grammar
  RegularExpression→Grammar  ⊥-Reg = ⊥-grammar
  RegularExpression→Grammar (g ⊗Reg g') =
    (RegularExpression→Grammar g) ⊗ (RegularExpression→Grammar g')
  RegularExpression→Grammar (literalReg c) = literal c
  RegularExpression→Grammar (g ⊕Reg g') =
    RegularExpression→Grammar g ⊕ RegularExpression→Grammar g'
  RegularExpression→Grammar (KL*Reg g) = KL* (RegularExpression→Grammar g)

