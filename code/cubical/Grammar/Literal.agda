open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Literal (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List

open import Grammar.Base Alphabet

private
  variable
    ℓG : Level

literal : ⟨ Alphabet ⟩ → Grammar ℓ-zero
literal c w = w ≡ [ c ]
