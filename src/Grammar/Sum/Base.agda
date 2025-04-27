{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Base Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓC ℓX : Level

⊕ᴰ : {X : Type ℓX} → (X → Grammar ℓA) → Grammar (ℓ-max ℓX ℓA)
⊕ᴰ {X = X} f w = Σ X λ x → f x w

syntax ⊕ᴰ {X = X}(λ x → A) = ⊕[ x ∈ X ] A
infix 8 ⊕ᴰ

module _ {X : Type ℓX} {A : X → Grammar ℓA} where
  σ : ∀ x → A x ⊢ ⊕[ x ∈ X ] A x
  σ x w z = x , z

module _ {X : Type ℓX} {A : Grammar ℓA}{B : X → Grammar ℓB} where
  ⊕ᴰ-elim : (∀ x → B x ⊢ A) → ⊕[ x ∈ X ] B x ⊢ A
  ⊕ᴰ-elim f w x = f (x .fst) w (x .snd)

  @0 ⊕ᴰ≡ : (f f' : (⊕[ x ∈ X ] B x) ⊢ A)
    → (∀ x → f ∘g σ x ≡ f' ∘g σ x)
    → f ≡ f'
  ⊕ᴰ≡ f f' fx≡fx' i w z = fx≡fx' (z .fst) i w (z .snd)

@0 ⊕ᴰ-elim∘g :
  ∀ {X : Type ℓX}{A : Grammar ℓA}
  {B : X → Grammar ℓB}{C : Grammar ℓC}
  → {f' : ∀ x → B x ⊢ A}
  → {f : A ⊢ C}
  → f ∘g ⊕ᴰ-elim f' ≡ ⊕ᴰ-elim (λ x → f ∘g f' x)
⊕ᴰ-elim∘g = ⊕ᴰ≡ _ _ (λ x → refl)

module _ {X : Type ℓX} {A : X → Grammar ℓA} {B : X → Grammar ℓB}
  (e : (x : X) → A x ⊢ B x)
  where

  map⊕ᴰ : ⊕[ x ∈ X ] A x ⊢ ⊕[ x ∈ X ] B x
  map⊕ᴰ = ⊕ᴰ-elim (λ x → σ x ∘g e x)

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
    ⊕ᴰ-elim (λ x → σ (f x))
    ∘g map⊕ᴰ e
