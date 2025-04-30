{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Parser.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

import Erased.Data.Sum.Base as Sum
open import Cubical.Data.Bool using (Bool ; true ; false)

open import Grammar Alphabet isSetAlphabet
open import Grammar.Maybe Alphabet isSetAlphabet
open import Term Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX ℓY : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

WeakParser : Grammar ℓA → Type ℓA
WeakParser A = string ⊢ Maybe A

runWeakParser : WeakParser A → (w : String) → (Maybe A) w
runWeakParser f w = f w (mkstring w)

record Parser (A : Grammar ℓA) (B : Grammar ℓB) : Type (ℓ-max ℓA ℓB) where
  field
    @0 disj : disjoint A B
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
open WeakEquivalence

module _ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC}
  (P : Parser A B) (A≈C : A ≈ C) where
  ≈Parser : Parser C B
  ≈Parser .disj = disjoint≈ (P .disj) A≈C
  ≈Parser .fun = A≈C .fun ,⊕p id ∘g P .fun
