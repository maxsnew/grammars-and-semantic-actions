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
  variable ℓG ℓG' ℓB ℓA ℓg ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

module _ where
  data Functor (A : Type ℓA) : Level → Typeω where
    k : (g : Grammar ℓg) → Functor A ℓg
    Var : (a : A) → Functor A ℓA -- reference one of the mutually inductive types being defined
    &e ⊕e : ∀ {ℓ} (B : Type ℓB) → (F : B → Functor A ℓ) → Functor A (ℓ-max ℓB ℓ)
    ⊗e : ∀ {ℓ}{ℓ'} → (F : Functor A ℓ) → (F' : Functor A ℓ') → Functor A (ℓ-max ℓ ℓ')

  module _ {A : Type ℓA} where
    ⟦_⟧ : ∀ {ℓ}{ℓ'} → Functor A ℓ → (A → Grammar ℓ') → Grammar (ℓ-max ℓ ℓ')
    ⟦_⟧ {ℓ' = ℓ'} (k h) g = LiftG ℓ' h
    ⟦ Var a ⟧ g = LiftG ℓA (g a)
    ⟦ &e B F ⟧ g = &[ b ∈ B ] ⟦ F b ⟧ g
    ⟦ ⊕e B F ⟧ g = ⊕[ b ∈ B ] ⟦ F b ⟧ g
    ⟦ ⊗e F F' ⟧ g = ⟦ F ⟧ g ⊗ ⟦ F' ⟧ g

  map : ∀ {A : Type ℓ}{ℓ'}(F : Functor A ℓ')
          {g : A → Grammar ℓ''}{h : A → Grammar ℓ'''}
        → (∀ a → g a ⊢ h a)
        → ⟦ F ⟧ g ⊢ ⟦ F ⟧ h
  map (k g) f = liftG ∘g lowerG
  map (Var a) f = liftG ∘g f a ∘g lowerG
  map (&e B F) f = &ᴰ-intro λ a → map (F a) f ∘g &ᴰ-π a
  map (⊕e B F) f = ⊕ᴰ-elim λ a → ⊕ᴰ-in a ∘g map (F a) f
  map (⊗e F F') f = map F f ,⊗ map F' f

  module _ {A : Type ℓ} where
    opaque
      unfolding _⊗_ ⊗-intro

      map-id : ∀ {ℓ'} (F : Functor A ℓ') {g : A → Grammar ℓ''} →
        map F (λ a → id {g = g a}) ≡ id
      map-id (k g) i = id
      map-id (Var a) i = id
      map-id (&e B F) i = &ᴰ-intro (λ a → map-id (F a) i ∘g &ᴰ-π a)
      map-id (⊕e B F) i = ⊕ᴰ-elim (λ a → ⊕ᴰ-in a ∘g map-id (F a) i)
      map-id (⊗e F F') i = map-id F i ,⊗ map-id F' i

      map-∘ :  ∀ {ℓ'} {g : A → Grammar ℓ''}{h : A → Grammar ℓ'''}{k : A → Grammar ℓ''''}
        (F : Functor A ℓ')
        (f : ∀ a → h a  ⊢ k a)(f' : ∀ a → g a ⊢ h a)
        → map F (λ a → f a ∘g f' a) ≡ map F f ∘g map F f'
      map-∘ (k g) f f' i = liftG ∘g lowerG
      map-∘ (Var a) f f' i = liftG ∘g f a ∘g f' a ∘g lowerG
      map-∘ (&e B F) f f' i = &ᴰ-intro (λ a → map-∘ (F a) f f' i ∘g &ᴰ-π a)
      map-∘ (⊕e B F) f f' i = ⊕ᴰ-elim (λ a → ⊕ᴰ-in a ∘g map-∘ (F a) f f' i)
      map-∘ (⊗e F F') f f' i = map-∘ F f f' i ,⊗ map-∘ F' f f' i
