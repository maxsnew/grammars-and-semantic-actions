open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Functor (Alphabet : hSet ℓ-zero)where

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

private
  variable ℓA ℓB ℓC ℓX : Level

module _ where
  data Functor (X : Type ℓX) : Type (ℓ-suc ℓX) where
    k : (A : Grammar ℓX) → Functor X
    Var : (x : X) → Functor X -- reference one of the mutually inductive types being defined
    &e ⊕e : ∀ (Y : Type ℓX) → (F : Y → Functor X) → Functor X
    ⊗e : (F : Functor X) → (F' : Functor X) → Functor X

  module _ {X : Type ℓX}{ℓA} where
    ⟦_⟧ : Functor X → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
    ⟦ k h ⟧ A = LiftG ℓA h
    ⟦ Var x ⟧ A = LiftG ℓX (A x)
    ⟦ &e Y F ⟧ A = &[ y ∈ Y ] ⟦ F y ⟧ A
    ⟦ ⊕e Y F ⟧ A = ⊕[ y ∈ Y ] ⟦ F y ⟧ A
    ⟦ ⊗e F F' ⟧ A = ⟦ F ⟧ A ⊗ ⟦ F' ⟧ A

  map : ∀ {X : Type ℓX}(F : Functor X) {A : X → Grammar ℓA}{B : X → Grammar ℓB}
        → (∀ x → A x ⊢ B x)
        → ⟦ F ⟧ A ⊢ ⟦ F ⟧ B
  map (k A) f = liftG ∘g lowerG
  map (Var x) f = liftG ∘g f x ∘g lowerG
  map (&e Y F) f = &ᴰ-in λ y → map (F y) f ∘g &ᴰ-π y
  map (⊕e Y F) f = ⊕ᴰ-elim λ y → ⊕ᴰ-in y ∘g map (F y) f
  map (⊗e F F') f = map F f ,⊗ map F' f

  module _ {X : Type ℓX} where
    opaque
      unfolding _⊗_ ⊗-intro

      map-id : ∀ (F : Functor X) {A : X → Grammar ℓA} →
        map F (λ x → id {A = A x}) ≡ id
      map-id (k A) i = id
      map-id (Var x) i = id
      map-id (&e Y F) i = &ᴰ-in (λ y → map-id (F y) i ∘g &ᴰ-π y)
      map-id (⊕e Y F) i = ⊕ᴰ-elim (λ y → ⊕ᴰ-in y ∘g map-id (F y) i)
      map-id (⊗e F F') i = map-id F i ,⊗ map-id F' i

      map-∘ :  ∀ {A : X → Grammar ℓA}{B : X → Grammar ℓB}{C : X → Grammar ℓC}
        (F : Functor X)
        (f : ∀ x → B x  ⊢ C x)(f' : ∀ x → A x ⊢ B x)
        → map F (λ x → f x ∘g f' x) ≡ map F f ∘g map F f'
      map-∘ (k A) f f' i = liftG ∘g lowerG
      map-∘ (Var x) f f' i = liftG ∘g f x ∘g f' x ∘g lowerG
      map-∘ (&e Y F) f f' i = &ᴰ-in (λ y → map-∘ (F y) f f' i ∘g &ᴰ-π y)
      map-∘ (⊕e Y F) f f' i = ⊕ᴰ-elim (λ y → ⊕ᴰ-in y ∘g map-∘ (F y) f f' i)
      map-∘ (⊗e F F') f f' i = map-∘ F f f' i ,⊗ map-∘ F' f f' i
