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
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' : Level

module _ {A : Type ℓ} (F : A → Functor A) where
  open StrongEquivalence

  unroll≅ : ∀ a → μ F a ≅ ⟦ F a ⟧ (μ F)
  unroll≅ a .fun = unroll F a
  unroll≅ a .inv = roll
  unroll≅ a .sec = refl
  unroll≅ a .ret =
    equalizer-ind
      F
      (λ a → μ F a)
      (λ a → roll ∘g unroll F a)
      (λ _ → id)
      (λ a → refl)
      a
