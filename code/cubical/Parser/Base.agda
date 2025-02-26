open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Parser.Base (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Term Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

record Parser (A : Grammar ℓA) : Type (ℓ-suc ℓA) where
  field
    compl : Grammar ℓA
    compl-disjoint : disjoint A compl
    fun : string ⊢ A ⊕ compl
