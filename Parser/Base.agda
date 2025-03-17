open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Parser.Base (Alphabet : hSet ℓ-zero) where

import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool using (Bool ; true ; false)

open import Grammar Alphabet
open import Term Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX ℓY : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

record Parser (A : Grammar ℓA) : Type (ℓ-suc ℓA) where
  field
    compl : Grammar ℓA
    compl-disjoint : disjoint A compl
    fun : string ⊢ A ⊕ compl

  -- Utilities to benchmark a Parser
  module _ where
    opaque
      unfolding _⊕_
      run : (w : String) → (A w) Sum.⊎ (compl w)
      run w = fun w (mkstring w)


    private
      is-inl? : ∀ {X : Type ℓX} {Y : Type ℓY} →
        X Sum.⊎ Y → Bool
      is-inl? (Sum.inl x) = true
      is-inl? (Sum.inr y) = false

    accept? : (w : String) → Bool
    accept? w = is-inl? (run w)

open Parser
open LogicalEquivalence

module _ {A B : Grammar ℓA} (P : Parser A) (A≈B : A ≈ B) where
  ≈Parser : Parser B
  ≈Parser .compl = P .compl
  ≈Parser .compl-disjoint = disjoint≈ (P .compl-disjoint) A≈B
  ≈Parser .fun = A≈B .fun ,⊕p id ∘g P .fun
