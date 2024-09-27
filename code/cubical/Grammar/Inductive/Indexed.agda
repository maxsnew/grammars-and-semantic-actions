{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Indexed (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Helper
open import Grammar Alphabet
open import Term Alphabet

private
  variable ℓG ℓG' ℓ ℓ' : Level

module _ where
  data Functor (A : Type ℓ) : Type (ℓ-suc ℓ) where
    k : (g : Grammar ℓ) → Functor A
    Var : (a : A) → Functor A -- reference one of the mutually inductive types being defined
    &e ⊕e : ∀ (B : Type ℓ) → (F : B → Functor A) → Functor A
    ⊗e : (F : Functor A) → (F' : Functor A) → Functor A

  ⟦_⟧ : {A : Type ℓ} → Functor A → (A → Grammar ℓ) → Grammar ℓ
  ⟦ k h ⟧ g = h
  ⟦ Var a ⟧ g = g a
  ⟦ &e B F ⟧ g = &[ b ∈ B ] ⟦ F b ⟧ g
  ⟦ ⊕e B F ⟧ g = ⊕[ b ∈ B ] ⟦ F b ⟧ g
  ⟦ ⊗e F F' ⟧ g = ⟦ F ⟧ g ⊗ ⟦ F' ⟧ g

  map : ∀ {A : Type ℓ}(F : Functor A) {g h : A → Grammar ℓ}
        → (∀ a → g a ⊢ h a)
        → ⟦ F ⟧ g ⊢ ⟦ F ⟧ h
  map (k g) f = id
  map (Var a) f = f a
  map (&e B F) f = &ᴰ-intro λ a → map (F a) f ∘g &ᴰ-π a
  map (⊕e B F) f = ⊕ᴰ-elim λ a → ⊕ᴰ-in a ∘g map (F a) f
  map (⊗e F F') f = map F f ,⊗ map F' f

  module _ {A : Type ℓ} where
    opaque
      unfolding _⊗_ ⊗-intro

      map-id : ∀ (F : Functor A) {g : A → Grammar _} →
        map F (λ a → id {g = g a}) ≡ id
      map-id (k g) i = id
      map-id (Var a) i = id
      map-id (&e B F) i = LinΠ-intro (λ a → map-id (F a) i ∘g LinΠ-app a)
      map-id (⊕e B F) i = LinΣ-elim (λ a → LinΣ-intro a ∘g map-id (F a) i)
      map-id (⊗e F F') i = map-id F i ,⊗ map-id F' i

      map-∘ :  ∀ (F : Functor A) {g h k : A → Grammar _} (f : ∀ a → h a  ⊢ k a)(f' : ∀ a → g a ⊢ h a)
        → map F (λ a → f a ∘g f' a) ≡ map F f ∘g map F f'
      map-∘ (k g) f f' i = id
      map-∘ (Var a) f f' i = f a ∘g f' a
      map-∘ (&e B F) f f' i = LinΠ-intro (λ a → map-∘ (F a) f f' i ∘g LinΠ-app a)
      map-∘ (⊕e B F) f f' i = LinΣ-elim (λ a → LinΣ-intro a ∘g map-∘ (F a) f f' i)
      map-∘ (⊗e F F') f f' i = map-∘ F f f' i ,⊗ map-∘ F' f f' i

    {-# NO_POSITIVITY_CHECK #-}
    data μ (F : A → Functor A) a : Grammar ℓ where
      roll : ⟦ F a ⟧ (μ F) ⊢ μ F a

  module _ {A : Type ℓ} (F : A → Functor A) where
    Algebra : (A → Grammar ℓ) → Type _
    Algebra g = ∀ a → ⟦ F a ⟧ g ⊢ g a

    initialAlgebra : Algebra (μ F)
    initialAlgebra = λ a → roll

    Homomorphism : ∀ {g h} → Algebra g → Algebra h → Type _
    Homomorphism {g = g}{h} α β =
      Σ[ ϕ ∈ (∀ a → g a ⊢ h a) ]
      (∀ a → ϕ a ∘g α a ≡ β a ∘g map (F a) ϕ)

    idHomo : ∀ {g} → (α : Algebra g) → Homomorphism α α
    idHomo α = (λ a → id) , λ a → cong (α a ∘g_) (sym (map-id (F a)))

    compHomo : ∀ {g h k} (α : Algebra g)(β : Algebra h)(η : Algebra k)
      → Homomorphism β η → Homomorphism α β → Homomorphism α η
    compHomo α β η ϕ ψ .fst a = ϕ .fst a ∘g ψ .fst a
    compHomo α β η ϕ ψ .snd a =
      cong (ϕ .fst a ∘g_) (ψ .snd a)
      ∙ cong (_∘g map (F a) (ψ .fst)) (ϕ .snd a)
      ∙ cong (η a ∘g_) (sym (map-∘ (F a) (ϕ .fst) (ψ .fst)))

    {-# TERMINATING #-}
    recHomo : ∀ {g} → (α : Algebra g) → Homomorphism initialAlgebra α
    recHomo α .fst a w (roll ._ x) =
      α a w (map (F a) (recHomo α .fst) w x)
    recHomo α .snd a = refl

    rec : ∀ {g} → (α : Algebra g) → ∀ a → (μ F a) ⊢ g a
    rec α = recHomo α .fst

    module _ {g} (α : Algebra g) (ϕ : Homomorphism initialAlgebra α) where
      private
        {-# TERMINATING #-}
        μ-η' : ∀ a w x → ϕ .fst a w x ≡ rec α a w x
        μ-η' a w (roll _ x) =
          (λ i → ϕ .snd a i w x)
          ∙ λ i → α a w (map (F a) (λ a w x → μ-η' a w x i) w x)
      μ-η : ϕ .fst ≡ rec α
      μ-η = funExt (λ a → funExt λ w → funExt λ x → μ-η' a w x)

    ind : ∀ {g} (α : Algebra g) (ϕ ϕ' : Homomorphism initialAlgebra α) → ϕ .fst ≡ ϕ' .fst
    ind α ϕ ϕ' = μ-η α ϕ ∙ sym (μ-η α ϕ')

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
