open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓX : Level

&ᴰ : {X : Type ℓX} → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
&ᴰ {X = X} f w = ∀ (x : X) → f x w

syntax &ᴰ {X = X}(λ x → A) = &[ x ∈ X ] A
infix 7 &ᴰ

module _ {X : Type ℓX} {A : X → Grammar ℓA} where
  π : ∀ x → &[ x ∈ X ] A x ⊢ A x
  π x w f = f x

module _ {X : Type ℓX} {A : Grammar ℓA}{B : X → Grammar ℓB} where
  &ᴰ-intro : (∀ x → A ⊢ B x) → A ⊢ &[ x ∈ X ] B x
  &ᴰ-intro f w z x = f x w z

  &ᴰ≡ : (f f' : A ⊢ &[ x ∈ X ] B x)
    → (∀ x → π x ∘g f ≡ π x ∘g f')
    → f ≡ f'
  &ᴰ≡ f f' f≡ i w z x = f≡ x i w z

module _ {X : Type ℓX} {A : Grammar ℓA} where
  Δ : A ⊢ &[ x ∈ X ] A
  Δ = &ᴰ-intro (λ _ → id)

module _ {X : Type ℓX}
  {A : X → Grammar ℓA} {B : X → Grammar ℓB}
  (e : (x : X) → A x ⊢ B x)
  where
  map&ᴰ : &[ x ∈ X ] A x ⊢ &[ x ∈ X ] B x
  map&ᴰ = &ᴰ-intro λ x → e x ∘g π x

open StrongEquivalence

module _ {X : Type ℓX}
  {A : X → Grammar ℓA} {B : X → Grammar ℓB}
  (A≅B : ∀ (x : X) → A x ≅ B x)
  where

  &ᴰ≅ : (&[ x ∈ X ] A x) ≅ &[ x ∈ X ] B x
  &ᴰ≅ .fun = map&ᴰ λ x → A≅B x .fun
  &ᴰ≅ .inv = map&ᴰ λ x → A≅B x .inv
  &ᴰ≅ .sec = &ᴰ≡ _ _ λ x → cong (_∘g π x) (A≅B x .sec)
  &ᴰ≅ .ret = &ᴰ≡ _ _ λ x → cong (_∘g π x) (A≅B x .ret)

