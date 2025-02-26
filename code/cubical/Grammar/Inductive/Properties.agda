open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Equalizer Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term.Base Alphabet

private
  variable ℓA ℓB ℓX : Level

module _ {X : Type ℓX} (F : X → Functor X) where
  open StrongEquivalence

  unroll≅ : ∀ x → μ F x ≅ ⟦ F x ⟧ (μ F)
  unroll≅ x .fun = unroll F x
  unroll≅ x .inv = roll
  unroll≅ x .sec = refl
  unroll≅ x .ret =
    equalizer-ind
      F
      (λ x → μ F x)
      (λ x → roll ∘g unroll F x)
      (λ _ → id)
      (λ x → refl)
      x
