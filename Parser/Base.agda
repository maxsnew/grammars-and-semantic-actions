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

record Parser (A : Grammar ℓA) (B : Grammar ℓB) : Type (ℓ-max ℓA ℓB) where
  field
    disj : disjoint A B
    fun : string ⊢ A ⊕ B

  -- Utilities to benchmark a Parser
  module _ where
    opaque
      unfolding _⊕_
      run : (w : String) → (A w) Sum.⊎ (B w)
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

module _ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC}
  (P : Parser A B) (A≈C : A ≈ C) where
  ≈Parser : Parser C B
  ≈Parser .disj = disjoint≈ (P .disj) A≈C
  ≈Parser .fun = A≈C .fun ,⊕p id ∘g P .fun
