open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Liftless.Functor (Alphabet : hSet ℓ-zero)where

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

  ⟦_⟧ : {X : Type ℓX} → Functor X → (X → Grammar ℓX) → Grammar ℓX
  ⟦ k B ⟧ A = B
  ⟦ Var x ⟧ A = A x
  ⟦ &e Y F ⟧ A = &[ y ∈ Y ] ⟦ F y ⟧ A
  ⟦ ⊕e Y F ⟧ A = ⊕[ y ∈ Y ] ⟦ F y ⟧ A
  ⟦ F ⊗e F' ⟧ A = ⟦ F ⟧ A ⊗ ⟦ F' ⟧ A
  ⟦ F &e2 F' ⟧ A = ⟦ F ⟧ A & ⟦ F' ⟧ A

  map : ∀ {X : Type ℓX}(F : Functor X) {A}{B}
        → (∀ x → A x ⊢ B x)
        → ⟦ F ⟧ A ⊢ ⟦ F ⟧ B
  map (k A) f = id
  map (Var x) f = f x
  map (&e Y F) f = &ᴰ-intro λ y → map (F y) f ∘g π y
  map (⊕e Y F) f = ⊕ᴰ-elim λ y → σ y ∘g map (F y) f
  map (F ⊗e F') f = map F f ,⊗ map F' f
  map (F &e2 F') f = map F f ,&p map F' f

  module _ {X : Type ℓX} where
    opaque
      unfolding _⊗_ ⊗-intro &-intro π₁

      map-id : ∀ (F : Functor X) {A : X → Grammar _} →
        map F (λ x → id {A = A x}) ≡ id
      map-id (k A) i = id
      map-id (Var x) i = id
      map-id (&e Y F) i = &ᴰ-intro (λ y → map-id (F y) i ∘g π y)
      map-id (⊕e Y F) i = ⊕ᴰ-elim (λ y → σ y ∘g map-id (F y) i)
      map-id (F ⊗e F') i = map-id F i ,⊗ map-id F' i
      map-id (F &e2 F') i = map-id F i ,&p map-id F' i

      map-∘ :  ∀ {A B C : X → Grammar _}
        (F : Functor X)
        (f : ∀ x → B x  ⊢ C x)(f' : ∀ x → A x ⊢ B x)
        → map F (λ x → f x ∘g f' x) ≡ map F f ∘g map F f'
      map-∘ (k A) f f' i = id
      map-∘ (Var x) f f' i = f x ∘g f' x
      map-∘ (&e Y F) f f' i = &ᴰ-intro (λ y → map-∘ (F y) f f' i ∘g π y)
      map-∘ (⊕e Y F) f f' i = ⊕ᴰ-elim (λ y → σ y ∘g map-∘ (F y) f f' i)
      map-∘ (F ⊗e F') f f' i = map-∘ F f f' i ,⊗ map-∘ F' f f' i
      map-∘ (F &e2 F') f f' i = map-∘ F f f' i ,&p map-∘ F' f f' i

  module _ {X : Type ℓX} (F : X → Functor X) where
    Algebra : (X → Grammar ℓX) → Type ℓX
    Algebra A = ∀ x → ⟦ F x ⟧ A ⊢ A x

    module _ {A B} (α : Algebra A) (β : Algebra B) where
      isHomo : (∀ x → A x ⊢ B x) → Type _
      isHomo ϕ = (∀ x → ϕ x ∘g α x ≡ β x ∘g map (F x) ϕ)

      Homomorphism : Type _
      Homomorphism = Σ _ isHomo

    idHomo : ∀ {A} → (α : Algebra A) → Homomorphism α α
    idHomo α = (λ x → id) , λ x → cong (α x ∘g_) (sym (map-id (F x)))

    compHomo : ∀ {A B C}
      (α : Algebra A)(β : Algebra B)(η : Algebra C)
      → Homomorphism β η → Homomorphism α β → Homomorphism α η
    compHomo α β η ϕ ψ .fst x = ϕ .fst x ∘g ψ .fst x
    compHomo α β η ϕ ψ .snd x =
      cong (ϕ .fst x ∘g_) (ψ .snd x)
      ∙ cong (_∘g map (F x) (ψ .fst)) (ϕ .snd x)
      ∙ cong (η x ∘g_) (sym (map-∘ (F x) (ϕ .fst) (ψ .fst)))

  -- Functor here is an expression monad whose intended semantics is a
  -- continuation monad.
  -- i.e., Functor X is thought of as (X →
  -- Grammar) → Grammar
  retF : ∀ {X : Type ℓX} → X → Functor X
  retF x = Var x

  _>>=F_ : {X Y : Type ℓX} → Functor X → (X → Functor Y) → Functor Y
  k A >>=F K = k A
  Var x >>=F K = K x
  &e Y' F >>=F K = &e Y' (λ y' → F y' >>=F K)
  ⊕e Y' F >>=F K = ⊕e Y' (λ y' → F y' >>=F K)
  (F ⊗e F') >>=F K = (F >>=F K) ⊗e (F' >>=F K)
  (F &e2 F') >>=F K = (F >>=F K) &e2 (F' >>=F K)

  ⟦⟧>>= : ∀ {X Y : Type ℓX} (F : Functor X) (K : X → Functor Y)
    → ⟦ F >>=F K ⟧ ≡ λ A_y → ⟦ F ⟧ (λ x → ⟦ K x ⟧ A_y)
  ⟦⟧>>= (k A) K = refl
  ⟦⟧>>= (Var x) K = refl
  ⟦⟧>>= (&e Y F) K = funExt λ A → cong &ᴰ (funExt λ y → funExt⁻ (⟦⟧>>= (F y) K) A)
  ⟦⟧>>= (⊕e Y F) K = funExt λ A → cong ⊕ᴰ (funExt λ y → funExt⁻ (⟦⟧>>= (F y) K) A)
  ⟦⟧>>= (F ⊗e F') K = funExt λ A → cong₂ _⊗_ (funExt⁻ (⟦⟧>>= F K) A) (funExt⁻ (⟦⟧>>= F' K) A)
  ⟦⟧>>= (F &e2 F') K = funExt λ A → cong₂ _&_ (funExt⁻ (⟦⟧>>= F K) A) (funExt⁻ (⟦⟧>>= F' K) A)

  _>=>F_ : {X Y Z : Type ℓX} → (X → Functor Y) → (Y → Functor Z) → X → Functor Z
  (F >=>F G) x = F x >>=F G
