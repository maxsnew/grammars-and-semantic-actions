{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module @0 Grammar.Inductive.AsPath.Indexed (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.LinearProduct.AsPath.Base Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

open import Grammar.Inductive.Functor Alphabet public

private
  variable ℓA ℓB ℓC ℓX : Level

module _ where
  module _ {X : Type ℓX}{ℓA} where
    ⟦_⟧ : Functor X → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
    ⟦ k B ⟧ A = LiftG ℓA B
    ⟦ Var x ⟧ A = LiftG ℓX (A x)
    ⟦ &e Y F ⟧ A = &[ y ∈ Y ] ⟦ F y ⟧ A
    ⟦ ⊕e Y F ⟧ A = ⊕[ y ∈ Y ] ⟦ F y ⟧ A
    ⟦ F ⊗e F' ⟧ A = ⟦ F ⟧ A ⊗ ⟦ F' ⟧ A
    ⟦ F &e2 F' ⟧ A = ⟦ F ⟧ A & ⟦ F' ⟧ A

  map : ∀ {X : Type ℓX}(F : Functor X) {A : X → Grammar ℓA}{B : X → Grammar ℓB}
        → (∀ x → A x ⊢ B x)
        → ⟦ F ⟧ A ⊢ ⟦ F ⟧ B
  map (k A) f = liftG ∘g lowerG
  map (Var x) f = liftG ∘g f x ∘g lowerG
  map (&e Y F) f = &ᴰ-intro λ y → map (F y) f ∘g π y
  map (⊕e Y F) f = ⊕ᴰ-elim λ y → σ y ∘g map (F y) f
  map (F ⊗e F') f = map F f ,⊗ map F' f
  map (F &e2 F') f = map F f ,&p map F' f

  module _ {X : Type ℓX} where
    opaque
      unfolding _⊗_ ⊗-intro &-intro π₁

      map-id : ∀ (F : Functor X) {A : X → Grammar ℓA} →
        map F (λ x → id {A = A x}) ≡ id
      map-id (k A) i = id
      map-id (Var x) i = id
      map-id (&e Y F) i = &ᴰ-intro (λ y → map-id (F y) i ∘g π y)
      map-id (⊕e Y F) i = ⊕ᴰ-elim (λ y → σ y ∘g map-id (F y) i)
      map-id (F ⊗e F') i = map-id F i ,⊗ map-id F' i
      map-id (F &e2 F') i = map-id F i ,&p map-id F' i

      map-∘ :  ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB}{C : X → Grammar ℓC}
        (F : Functor X)
        (f : ∀ x → B x  ⊢ C x)(f' : ∀ x → A x ⊢ B x)
        → map F (λ x → f x ∘g f' x) ≡ map F f ∘g map F f'
      map-∘ (k A) f f' i = liftG ∘g lowerG
      map-∘ (Var x) f f' i = liftG ∘g f x ∘g f' x ∘g lowerG
      map-∘ (&e Y F) f f' i = &ᴰ-intro (λ y → map-∘ (F y) f f' i ∘g π y)
      map-∘ (⊕e Y F) f f' i = ⊕ᴰ-elim (λ y → σ y ∘g map-∘ (F y) f f' i)
      map-∘ (F ⊗e F') f f' i = map-∘ F f f' i ,⊗ map-∘ F' f f' i
      map-∘ (F &e2 F') f f' i = map-∘ F f f' i ,&p map-∘ F' f f' i

  module _ {X : Type ℓX} (F : X → Functor X) where
    Algebra : (X → Grammar ℓA) → Type (ℓ-max ℓX ℓA)
    Algebra A = ∀ x → ⟦ F x ⟧ A ⊢ A x

    module _ {A : X → Grammar ℓA}{B : X → Grammar ℓB} (α : Algebra A) (β : Algebra B) where
      isHomo : (∀ x → A x ⊢ B x) → Type _
      isHomo ϕ = (∀ x → ϕ x ∘g α x ≡ β x ∘g map (F x) ϕ)

      Homomorphism : Type _
      Homomorphism = Σ _ isHomo

    idHomo : ∀ {A : X → Grammar ℓA} → (α : Algebra A) → Homomorphism α α
    idHomo α = (λ x → id) , λ x → cong (α x ∘g_) (sym (map-id (F x)))

    compHomo : ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB}{C : X → Grammar ℓC}
      (α : Algebra A)(β : Algebra B)(η : Algebra C)
      → Homomorphism β η → Homomorphism α β → Homomorphism α η
    compHomo α β η ϕ ψ .fst x = ϕ .fst x ∘g ψ .fst x
    compHomo α β η ϕ ψ .snd x =
      cong (ϕ .fst x ∘g_) (ψ .snd x)
      ∙ cong (_∘g map (F x) (ψ .fst)) (ϕ .snd x)
      ∙ cong (η x ∘g_) (sym (map-∘ (F x) (ϕ .fst) (ψ .fst)))

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
