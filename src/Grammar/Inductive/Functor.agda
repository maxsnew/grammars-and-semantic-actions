open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Functor (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

private
  variable ℓA ℓB ℓC ℓX : Level

module _ where
  data Functor (X : Type ℓX) : Type (ℓ-suc ℓX) where
    k : (A : Grammar ℓX) → Functor X
    Var : (x : X) → Functor X -- reference one of the mutually inductive types being defined
    &e ⊕e : ∀ (Y : Type ℓX) → (F : Y → Functor X) → Functor X
    _⊗e_ : (F : Functor X) → (F' : Functor X) → Functor X
    _&e2_ : (F : Functor X) → (F' : Functor X) → Functor X

  infixr 25 _⊗e_

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
