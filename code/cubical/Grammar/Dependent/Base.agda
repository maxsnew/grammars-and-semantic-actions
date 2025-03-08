open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet


private
  variable
    ℓA ℓB ℓC ℓX : Level

&ᴰ : {X : Type ℓX} → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
&ᴰ {X = X} f w = ∀ (x : X) → f x w

⊕ᴰ : {X : Type ℓX} → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
⊕ᴰ {X = X} f w = Σ[ x ∈ X ] f x w

syntax ⊕ᴰ {X = X}(λ x → A) = ⊕[ x ∈ X ] A
infix 8 ⊕ᴰ

syntax &ᴰ {X = X}(λ x → A) = &[ x ∈ X ] A
infix 7 &ᴰ

module _ {X : Type ℓX} {A : X → Grammar ℓA} where
  &ᴰ-π : ∀ x → &[ x ∈ X ] A x ⊢ A x
  &ᴰ-π x w f = f x

  ⊕ᴰ-in : ∀ x → A x ⊢ ⊕[ x ∈ X ] A x
  ⊕ᴰ-in x w z = x , z

module _ {X : Type ℓX} {A : Grammar ℓA}{B : X → Grammar ℓB} where
  &ᴰ-in : (∀ x → A ⊢ B x) → A ⊢ &[ x ∈ X ] B x
  &ᴰ-in f w z x = f x w z

  ⊕ᴰ-elim : (∀ x → B x ⊢ A) → ⊕[ x ∈ X ] B x ⊢ A
  ⊕ᴰ-elim f w x = f (x .fst) w (x .snd)

  ⊕ᴰ≡ : (f f' : (⊕[ x ∈ X ] B x) ⊢ A)
    → (∀ x → f ∘g ⊕ᴰ-in x ≡ f' ∘g ⊕ᴰ-in x)
    → f ≡ f'
  ⊕ᴰ≡ f f' fx≡fx' i w z = fx≡fx' (z .fst) i w (z .snd)

  &ᴰ≡ : (f f' : A ⊢ &[ x ∈ X ] B x)
    → (∀ x → &ᴰ-π x ∘g f ≡ &ᴰ-π x ∘g f')
    → f ≡ f'
  &ᴰ≡ f f' f≡ i w z x = f≡ x i w z

⊕ᴰ-elim∘g :
  ∀ {X : Type ℓX}{A : Grammar ℓA}
  {B : X → Grammar ℓB}{C : Grammar ℓC}
  → {f' : ∀ x → B x ⊢ A}
  → {f : A ⊢ C}
  → f ∘g ⊕ᴰ-elim f' ≡ ⊕ᴰ-elim (λ x → f ∘g f' x)
⊕ᴰ-elim∘g = ⊕ᴰ≡ _ _ (λ x → refl)

module _
  {X : Type ℓX}
  {A : X → Grammar ℓA}
  {B : X → Grammar ℓB}
  (e : (x : X) → A x ⊢ B x)
  where

  map⊕ᴰ : ⊕[ x ∈ X ] A x ⊢ ⊕[ x ∈ X ] B x
  map⊕ᴰ = ⊕ᴰ-elim (λ x → ⊕ᴰ-in x ∘g e x)

  map&ᴰ : &[ x ∈ X ] A x ⊢ &[ x ∈ X ] B x
  map&ᴰ = &ᴰ-in λ x → e x ∘g &ᴰ-π x

module _
  {X : Type ℓX}
  {Y : Type ℓX}
  {A : X → Grammar ℓA}
  {B : Y → Grammar ℓB}
  (f : X → Y)
  (e : (x : X) → A x ⊢ B (f x))
  where

  mapFst⊕ᴰ : ⊕[ x ∈ X ] A x ⊢ ⊕[ y ∈ Y ] B y
  mapFst⊕ᴰ =
    ⊕ᴰ-elim (λ x → ⊕ᴰ-in (f x))
    ∘g map⊕ᴰ e
