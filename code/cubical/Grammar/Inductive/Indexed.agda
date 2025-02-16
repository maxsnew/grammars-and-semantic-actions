{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Indexed (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Helper
open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

open import Grammar.Inductive.Functor Alphabet public

private
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

module _ where
  module _ {A : Type ℓ}{ℓ'} where
    -- NOTE: this is only needed because ⊗ is opaque. If it's not
    -- opaque this passes the positivity check.
    -- https://github.com/agda/agda/issues/6970
    {-# NO_POSITIVITY_CHECK #-}
    data μ (F : A → Functor A ℓ') a : Grammar (ℓ-max ℓ ℓ') where
      roll : ⟦ F a ⟧ (μ F) ⊢ μ F a

  module _ {A : Type ℓ}{ℓ'} (F : A → Functor A ℓ') where
    Algebra : (A → Grammar ℓ'') → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
    Algebra g = ∀ a → ⟦ F a ⟧ g ⊢ g a

    initialAlgebra : Algebra (μ F)
    initialAlgebra = λ a → roll

    Homomorphism : ∀ {g : A → Grammar ℓ''}{h : A → Grammar ℓ'''} → Algebra g → Algebra h → Type _
    Homomorphism {g = g}{h} α β =
      Σ[ ϕ ∈ (∀ a → g a ⊢ h a) ]
      (∀ a → ϕ a ∘g α a ≡ β a ∘g map (F a) ϕ)

    idHomo : ∀ {g : A → Grammar ℓ''} → (α : Algebra g) → Homomorphism α α
    idHomo α = (λ a → id) , λ a → cong (α a ∘g_) (sym (map-id (F a)))

    compHomo : ∀ {g : A → Grammar ℓ''}{h : A → Grammar ℓ'''}{k : A → Grammar ℓ''''}
      (α : Algebra g)(β : Algebra h)(η : Algebra k)
      → Homomorphism β η → Homomorphism α β → Homomorphism α η
    compHomo α β η ϕ ψ .fst a = ϕ .fst a ∘g ψ .fst a
    compHomo α β η ϕ ψ .snd a =
      cong (ϕ .fst a ∘g_) (ψ .snd a)
      ∙ cong (_∘g map (F a) (ψ .fst)) (ϕ .snd a)
      ∙ cong (η a ∘g_) (sym (map-∘ (F a) (ϕ .fst) (ψ .fst)))

    module _ {g : A → Grammar ℓ''} (α : Algebra g) where
      {-# TERMINATING #-}
      recHomo : Homomorphism initialAlgebra α
      recHomo .fst a w (roll ._ x) =
        α a w (map (F a) (recHomo .fst) w x)
      recHomo .snd a = refl

      rec : ∀ a → (μ F a) ⊢ g a
      rec = recHomo .fst

      module _ (ϕ : Homomorphism initialAlgebra α) where
        private
          {-# TERMINATING #-}
          μ-η' : ∀ a w x → ϕ .fst a w x ≡ rec a w x
          μ-η' a w (roll _ x) =
            (λ i → ϕ .snd a i w x)
            ∙ λ i → α a w (map (F a) (λ a w x → μ-η' a w x i) w x)
        μ-η : ϕ .fst ≡ rec
        μ-η = funExt (λ a → funExt λ w → funExt λ x → μ-η' a w x)

      ind : (ϕ ϕ' : Homomorphism initialAlgebra α) → ϕ .fst ≡ ϕ' .fst
      ind ϕ ϕ' = μ-η ϕ ∙ sym (μ-η ϕ')

      ind' : ∀ (ϕ ϕ' : Homomorphism initialAlgebra α) → ∀ a → ϕ .fst a ≡ ϕ' .fst a
      ind' ϕ ϕ' = funExt⁻ (ind ϕ ϕ')

    ind-id : ∀ (ϕ : Homomorphism initialAlgebra initialAlgebra) → ϕ .fst ≡ idHomo initialAlgebra .fst
    ind-id ϕ = ind initialAlgebra ϕ (idHomo initialAlgebra)

    ind-id' : ∀ (ϕ : Homomorphism initialAlgebra initialAlgebra) a → ϕ .fst a ≡ id
    ind-id' ϕ a = funExt⁻ (ind-id ϕ) a

    unroll : ∀ a → μ F a ⊢ ⟦ F a ⟧ (μ F)
    unroll a w (roll .w x) = x

    -- Lambek's lemma for indexed inductives
    unroll' : ∀ a → μ F a ⊢ ⟦ F a ⟧ (μ F)
    unroll' = rec {g = λ a → ⟦ F a ⟧ (μ F)} alg where
      alg : Algebra (λ a → ⟦ F a ⟧ (μ F))
      alg a = map (F a) (λ _ → roll)
