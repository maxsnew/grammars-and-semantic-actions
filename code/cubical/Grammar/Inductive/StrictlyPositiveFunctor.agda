{-

  A syntactic universe of strictly positive endofunctors Type^A → Type

  Used to define indexed inductive datatypes.

-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.StrictlyPositiveFunctor (Alphabet : hSet ℓ-zero)where

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
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' : Level

module _ where
  data Functor (A : Type ℓ) : Type (ℓ-suc ℓ) where
    k : (g : Grammar ℓ) → Functor A
    Var : (a : A) → Functor A -- reference one of the mutually inductive types being defined
    &e ⊕e : ∀ (B : Type ℓ) → (F : B → Functor A) → Functor A
    ⊗e : (F : Functor A) → (F' : Functor A) → Functor A

  module _ {A : Type ℓ}{ℓ'} where
    ⟦_⟧ : Functor A → (A → Grammar ℓ') → Grammar (ℓ-max ℓ ℓ')
    ⟦ k h ⟧ g = LiftG ℓ' h
    ⟦ Var a ⟧ g = LiftG ℓ (g a)
    ⟦ &e B F ⟧ g = &[ b ∈ B ] ⟦ F b ⟧ g
    ⟦ ⊕e B F ⟧ g = ⊕[ b ∈ B ] ⟦ F b ⟧ g
    ⟦ ⊗e F F' ⟧ g = ⟦ F ⟧ g ⊗ ⟦ F' ⟧ g

  map : ∀ {A : Type ℓ}(F : Functor A) {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}
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

      map-id : ∀ (F : Functor A) {g : A → Grammar ℓ'} →
        map F (λ a → id {g = g a}) ≡ id
      map-id (k g) i = id
      map-id (Var a) i = id
      map-id (&e B F) i = &ᴰ-intro (λ a → map-id (F a) i ∘g &ᴰ-π a)
      map-id (⊕e B F) i = ⊕ᴰ-elim (λ a → ⊕ᴰ-in a ∘g map-id (F a) i)
      map-id (⊗e F F') i = map-id F i ,⊗ map-id F' i

      map-∘ :  ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}{k : A → Grammar ℓ'''}
        (F : Functor A)
        (f : ∀ a → h a  ⊢ k a)(f' : ∀ a → g a ⊢ h a)
        → map F (λ a → f a ∘g f' a) ≡ map F f ∘g map F f'
      map-∘ (k g) f f' i = liftG ∘g lowerG
      map-∘ (Var a) f f' i = liftG ∘g f a ∘g f' a ∘g lowerG
      map-∘ (&e B F) f f' i = &ᴰ-intro (λ a → map-∘ (F a) f f' i ∘g &ᴰ-π a)
      map-∘ (⊕e B F) f f' i = ⊕ᴰ-elim (λ a → ⊕ᴰ-in a ∘g map-∘ (F a) f f' i)
      map-∘ (⊗e F F') f f' i = map-∘ F f f' i ,⊗ map-∘ F' f f' i
  module _ {A : Type ℓ} (F : A → Functor A) where
    Algebra : (A → Grammar ℓ') → Type (ℓ-max ℓ ℓ')
    Algebra g = ∀ a → ⟦ F a ⟧ g ⊢ g a
    Homomorphism : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''} → Algebra g → Algebra h → Type _
    Homomorphism {g = g}{h} α β =
      Σ[ ϕ ∈ (∀ a → g a ⊢ h a) ]
      (∀ a → ϕ a ∘g α a ≡ β a ∘g map (F a) ϕ)

    idHomo : ∀ {g : A → Grammar ℓ'} → (α : Algebra g) → Homomorphism α α
    idHomo α = (λ a → id) , λ a → cong (α a ∘g_) (sym (map-id (F a)))

    compHomo : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}{k : A → Grammar ℓ'''}
      (α : Algebra g)(β : Algebra h)(η : Algebra k)
      → Homomorphism β η → Homomorphism α β → Homomorphism α η
    compHomo α β η ϕ ψ .fst a = ϕ .fst a ∘g ψ .fst a
    compHomo α β η ϕ ψ .snd a =
      cong (ϕ .fst a ∘g_) (ψ .snd a)
      ∙ cong (_∘g map (F a) (ψ .fst)) (ϕ .snd a)
      ∙ cong (η a ∘g_) (sym (map-∘ (F a) (ϕ .fst) (ψ .fst)))

    -- module _ {g : A → Grammar ℓ'} (α : Algebra g) where
    --   isInitial
