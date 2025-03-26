{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Indexed (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

open import Grammar.Inductive.Functor Alphabet public

private
  variable ℓA ℓB ℓX : Level

module _ where
  module _ {X : Type ℓX} where
    -- NOTE: this is only needed because ⊗ is opaque. If it's not
    -- opaque this passes the positivity check.
    -- https://github.com/agda/agda/issues/6970
    {-# NO_POSITIVITY_CHECK #-}
    data μ (F : X → Functor X) x : Grammar ℓX where
      roll : ⟦ F x ⟧ (μ F) ⊢ μ F x

  module _ {X : Type ℓX} (F : X → Functor X) where
    initialAlgebra : Algebra F (μ F)
    initialAlgebra = λ x → roll

    module _ {A : X → Grammar ℓA} (α : Algebra F A) where
      {-# TERMINATING #-}
      recHomo : Homomorphism F initialAlgebra α
      recHomo .fst x w (roll ._ z) =
        α x w (map (F x) (recHomo .fst) w z)
      recHomo .snd x = refl

      rec : ∀ x → (μ F x) ⊢ A x
      rec = recHomo .fst

      module _ (ϕ : Homomorphism F initialAlgebra α) where
        private
          {-# TERMINATING #-}
          μ-η' : ∀ x w z → ϕ .fst x w z ≡ rec x w z
          μ-η' x w (roll _ z) =
            (λ i → ϕ .snd x i w z)
            ∙ λ i → α x w (map (F x) (λ x w z → μ-η' x w z i) w z)
        μ-η : ϕ .fst ≡ rec
        μ-η = funExt (λ x → funExt λ w → funExt λ z → μ-η' x w z)

      ind : (ϕ ϕ' : Homomorphism F initialAlgebra α) → ϕ .fst ≡ ϕ' .fst
      ind ϕ ϕ' = μ-η ϕ ∙ sym (μ-η ϕ')

      ind' : ∀ (ϕ ϕ' : Homomorphism F initialAlgebra α) → ∀ x → ϕ .fst x ≡ ϕ' .fst x
      ind' ϕ ϕ' = funExt⁻ (ind ϕ ϕ')

    ind-id : ∀ (ϕ : Homomorphism F initialAlgebra initialAlgebra) → ϕ .fst ≡ idHomo F initialAlgebra .fst
    ind-id ϕ = ind initialAlgebra ϕ (idHomo F initialAlgebra)

    ind-id' : ∀ (ϕ : Homomorphism F initialAlgebra initialAlgebra) x → ϕ .fst x ≡ id
    ind-id' ϕ x = funExt⁻ (ind-id ϕ) x

    unroll : ∀ x → μ F x ⊢ ⟦ F x ⟧ (μ F)
    unroll x w (roll .w z) = z

    -- Lambek's lemma for indexed inductives
    unroll' : ∀ x → μ F x ⊢ ⟦ F x ⟧ (μ F)
    unroll' = rec {A = λ x → ⟦ F x ⟧ (μ F)} alg where
      alg : Algebra F (λ x → ⟦ F x ⟧ (μ F))
      alg x = map (F x) (λ _ → roll)
