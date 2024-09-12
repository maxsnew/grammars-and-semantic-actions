open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Helper
open import Grammar Alphabet

private
  variable ℓG ℓG' : Level


module _ where
  data RegularExpression  : Type ℓ-zero where
    ε-Reg : RegularExpression
    ⊥-Reg : RegularExpression
    _⊗Reg_ : RegularExpression →
      RegularExpression → RegularExpression
    literalReg : ⟨ Alphabet ⟩ → RegularExpression
    _⊕Reg_ : RegularExpression → RegularExpression → RegularExpression
    KL*Reg : RegularExpression → RegularExpression

  RegularExpression→Grammar : RegularExpression → Grammar ℓ-zero
  RegularExpression→Grammar  ε-Reg = ε
  RegularExpression→Grammar  ⊥-Reg = ⊥
  RegularExpression→Grammar (g ⊗Reg g') =
    (RegularExpression→Grammar g) ⊗ (RegularExpression→Grammar g')
  RegularExpression→Grammar (literalReg c) = literal c
  RegularExpression→Grammar (g ⊕Reg g') =
    RegularExpression→Grammar g ⊕ RegularExpression→Grammar g'
  RegularExpression→Grammar (KL*Reg g) = KL* (RegularExpression→Grammar g)

