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

  module _ {A : Type ℓ} where
    map : ∀ (F : Functor A) {g h : A → Grammar ℓ}
      → (∀ a → g a ⊢ h a)
      → ⟦ F ⟧ g ⊢ ⟦ F ⟧ h
    map (k g) f = id
    map (Var a) f = f a
    map (&e B F) f = LinΠ-intro λ a → map (F a) f ∘g LinΠ-app a
    map (⊕e B F) f = LinΣ-elim λ a → LinΣ-intro a ∘g map (F a) f
    map (⊗e F F') f = map F f ,⊗ map F' f

    -- TODO: map-id, map-∘
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

    -- TODO: id, comp

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
  -- todo: induction principles
