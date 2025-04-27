{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.AsEquality.Indexed (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Product.Base Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.Base Alphabet isSetAlphabet
open import Grammar.Lift Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

open import Grammar.Inductive.Functor Alphabet isSetAlphabet public

private
  variable ℓA ℓB ℓC ℓX : Level

module _ where
  module _ {X : Type ℓX} where
    ⟦_⟧ : Functor X → {ℓA : Level} → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
    ⟦ k B ⟧ {ℓA = ℓA} A = LiftG ℓA B
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

      @0 map-id : ∀ (F : Functor X) {A : X → Grammar ℓA} →
        map F (λ x → id {A = A x}) ≡ id
      map-id (k A) i = id
      map-id (Var x) i = id
      map-id (&e Y F) i = &ᴰ-intro (λ y → map-id (F y) i ∘g π y)
      map-id (⊕e Y F) i = ⊕ᴰ-elim (λ y → σ y ∘g map-id (F y) i)
      map-id (F ⊗e F') i = map-id F i ,⊗ map-id F' i
      map-id (F &e2 F') i = map-id F i ,&p map-id F' i

      @0 map-∘ :  ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB}{C : X → Grammar ℓC}
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
      @0 isHomo : (∀ x → A x ⊢ B x) → Type _
      isHomo ϕ = (∀ x → ϕ x ∘g α x ≡ β x ∘g map (F x) ϕ)

      record Homomorphism : Type (ℓ-max ℓX (ℓ-max ℓA ℓB)) where
        field
          fun : ∀ x → A x ⊢ B x
          @0 is-homo : isHomo fun

    open Homomorphism

    idHomo : ∀ {A : X → Grammar ℓA} → (α : Algebra A) → Homomorphism α α
    idHomo α .fun x = id
    idHomo α .is-homo x = cong (α x ∘g_) (sym (map-id (F x)))

    compHomo : ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB}{C : X → Grammar ℓC}
      (α : Algebra A)(β : Algebra B)(η : Algebra C)
      → Homomorphism β η → Homomorphism α β → Homomorphism α η
    compHomo α β η ϕ ψ .fun x = ϕ .fun x ∘g ψ .fun x
    compHomo α β η ϕ ψ .is-homo x =
      cong (ϕ .fun x ∘g_) (ψ .is-homo x)
      ∙ cong (_∘g map (F x) (ψ .fun)) (ϕ .is-homo x)
      ∙ cong (η x ∘g_) (sym (map-∘ (F x) (ϕ .fun) (ψ .fun)))

  module _ {X : Type ℓX} where
    -- NOTE: this is only needed because ⊗ is opaque. If it's not
    -- opaque this passes the positivity check.
    -- https://github.com/agda/agda/issues/6970
    {-# NO_POSITIVITY_CHECK #-}
    data μ (F : X → Functor X) x : Grammar ℓX where
      roll : ⟦ F x ⟧ (μ F) ⊢ μ F x

  module _ {X : Type ℓX} (F : X → Functor X) where
    open Homomorphism

    initialAlgebra : Algebra F (μ F)
    initialAlgebra = λ x → roll

    module _ {A : X → Grammar ℓA} (α : Algebra F A) where
      {-# TERMINATING #-}
      recHomo : Homomorphism F initialAlgebra α
      recHomo .fun x w (roll ._ z) =
        α x w (map (F x) (recHomo .fun) w z)
      recHomo .is-homo x = refl

      rec : ∀ x → (μ F x) ⊢ A x
      rec = recHomo .fun

      module _ (ϕ : Homomorphism F initialAlgebra α) where
        private
          {-# TERMINATING #-}
          @0 μ-η' : ∀ x w z → ϕ .fun x w z ≡ rec x w z
          μ-η' x w (roll _ z) =
            (λ i → ϕ .is-homo x i w z)
            ∙ λ i → α x w (map (F x) (λ x w z → μ-η' x w z i) w z)
        @0 μ-η : ϕ .fun ≡ rec
        μ-η = funExt (λ x → funExt λ w → funExt λ z → μ-η' x w z)

      @0 ind : (ϕ ϕ' : Homomorphism F initialAlgebra α) → ϕ .fun ≡ ϕ' .fun
      ind ϕ ϕ' = μ-η ϕ ∙ sym (μ-η ϕ')

      @0 ind' : ∀ (ϕ ϕ' : Homomorphism F initialAlgebra α) → ∀ x → ϕ .fun x ≡ ϕ' .fun x
      ind' ϕ ϕ' = funExt⁻ (ind ϕ ϕ')

    @0 ind-id : ∀ (ϕ : Homomorphism F initialAlgebra initialAlgebra) → ϕ .fun ≡ idHomo F initialAlgebra .fun
    ind-id ϕ = ind initialAlgebra ϕ (idHomo F initialAlgebra)

    @0 ind-id' : ∀ (ϕ : Homomorphism F initialAlgebra initialAlgebra) x → ϕ .fun x ≡ id
    ind-id' ϕ x = funExt⁻ (ind-id ϕ) x

    unroll : ∀ x → μ F x ⊢ ⟦ F x ⟧ (μ F)
    unroll x w (roll .w z) = z

    -- Lambek's lemma for indexed inductives
    unroll' : ∀ x → μ F x ⊢ ⟦ F x ⟧ (μ F)
    unroll' = rec {A = λ x → ⟦ F x ⟧ (μ F)} alg where
      alg : Algebra F (λ x → ⟦ F x ⟧ (μ F))
      alg x = map (F x) (λ _ → roll)
