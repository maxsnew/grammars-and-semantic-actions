-- Distributivity of products over sums
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

module Grammar.Distributivity (Alphabet : hSet ℓ-zero) where

import Cubical.Data.Sum as Sum

open import Grammar.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Sum.Binary.Cartesian.Base Alphabet
open import Grammar.Product.Binary.Cartesian.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Function.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX ℓY : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

module _
  {X : Type ℓX}
  {Y : X → Type ℓY}
  {A : Σ[ x ∈ X ] Y x → Grammar ℓA}
  where
  -- Distributivity axiom
  &ᴰ⊕ᴰ-dist :
    (&[ x ∈ X ] (⊕[ y ∈ Y x ] A (x , y))) ⊢
      ⊕[ f ∈ (∀ (x : X) → Y x) ] (&[ x ∈ X ] A (x , f x))
  &ᴰ⊕ᴰ-dist _ z = fst ∘ z , snd ∘ z

  -- Derived inverse to the axiom
  &ᴰ⊕ᴰ-dist⁻ :
    ⊕[ f ∈ (∀ (x : X) → Y x) ] (&[ x ∈ X ] A (x , f x)) ⊢
      (&[ x ∈ X ] (⊕[ y ∈ Y x ] A (x , y)))
  &ᴰ⊕ᴰ-dist⁻ = ⊕ᴰ-elim (λ f → &ᴰ-intro λ x → σ (f x) ∘g π x)

  &ᴰ⊕ᴰ-dist≅  :
    (&[ x ∈ X ] (⊕[ y ∈ Y x ] A (x , y)))
      ≅
    (⊕[ f ∈ (∀ (x : X) → Y x) ] (&[ x ∈ X ] A (x , f x)))
  &ᴰ⊕ᴰ-dist≅ .fun = &ᴰ⊕ᴰ-dist
  &ᴰ⊕ᴰ-dist≅ .inv = &ᴰ⊕ᴰ-dist⁻
  &ᴰ⊕ᴰ-dist≅ .sec = refl
  &ᴰ⊕ᴰ-dist≅ .ret = refl

-- TODO : derive the following as an instance of the arbitrary
-- distributivity above

-- Distributivity of binary product over arbitrary sums
module _ {X : Type ℓX} {A : X → Grammar ℓA} {B : Grammar ℓB}
  where

  private
    the-fun : (⊕[ x ∈ X ] A x) & B ⊢ ⊕[ x ∈ X ] (A x & B)
    the-fun = ⇒-intro⁻ (⊕ᴰ-elim (λ x → ⇒-intro (σ x)))

    the-inv : ⊕[ x ∈ X ] (A x & B) ⊢ (⊕[ x ∈ X ] A x) & B
    the-inv = ⊕ᴰ-elim λ x → σ x ,&p id

    opaque
      unfolding ⇒-intro &-intro π₁
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec = refl

      the-ret : the-inv ∘g the-fun ≡ id
      the-ret = refl

  &⊕ᴰ-distL≅ :
    (⊕[ x ∈ X ] A x) & B ≅ ⊕[ x ∈ X ] (A x & B)
  &⊕ᴰ-distL≅ = mkStrEq the-fun the-inv the-sec the-ret

  &⊕ᴰ-distR≅ :
    B & (⊕[ x ∈ X ] A x) ≅ ⊕[ x ∈ X ] (B & A x)
  &⊕ᴰ-distR≅ =
    &-swap≅
    ≅∙ &⊕ᴰ-distL≅
    ≅∙ ⊕ᴰ≅ λ a → &-swap≅

-- Binary products over binary sums
module _ where
  &⊕-distR :
    (A ⊕ B) & C ⊢ (A & C) ⊕ (B & C)
  &⊕-distR = ⇒-intro⁻ (⊕-elim (⇒-intro inl) (⇒-intro inr))

  &⊕-distR⁻ :
    (A & B) ⊕ (C & B) ⊢ (A ⊕ C) & B
  &⊕-distR⁻ = ⊕-elim (inl ,&p id) (inr ,&p id)

  opaque
    unfolding _⊕_ ⇒-intro ⊕-elim π₁
    &⊕-distR-sec : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} →
      &⊕-distR {A = A}{B = C}{C = B} ∘g &⊕-distR⁻ ≡ id
    &⊕-distR-sec =
      funExt λ w → funExt λ { (Sum.inl x) → refl ; (Sum.inr x) → refl}
    &⊕-distR-ret : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} →
      &⊕-distR⁻ ∘g &⊕-distR {A = A}{B = C}{C = B} ≡ id
    &⊕-distR-ret =
      funExt λ w → funExt λ { (Sum.inl x , pB) → refl ; (Sum.inr x , pB) → refl}

  &⊕-distR≅ :
    StrongEquivalence
      ((A ⊕ C) & B)
      ((A & B) ⊕ (C & B))
  &⊕-distR≅ .fun = &⊕-distR
  &⊕-distR≅ .inv = &⊕-distR⁻
  &⊕-distR≅ .sec = &⊕-distR-sec
  &⊕-distR≅ .ret = &⊕-distR-ret

  &⊕-distL : A & (B ⊕ C) ⊢ (A & B) ⊕ (A & C)
  &⊕-distL =
    ⇒-intro⁻
      (⊕-elim
        (⇒-intro (inl ∘g &-swap))
        (⇒-intro (inr ∘g &-swap))) ∘g
    &-swap

  &⊕-distL⁻ : (A & B) ⊕ (A & C) ⊢ A & (B ⊕ C)
  &⊕-distL⁻ = ⊕-elim (id ,&p inl) (id ,&p inr)

  opaque
    unfolding _⊕_ ⇒-intro ⊕-elim π₁
    &⊕-distL-sec : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} →
      &⊕-distL {A = A}{B = C}{C = B} ∘g &⊕-distL⁻ ≡ id
    &⊕-distL-sec =
      funExt λ w → funExt λ { (Sum.inl x) → refl ; (Sum.inr x) → refl}
    &⊕-distL-ret : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC} →
      &⊕-distL⁻ ∘g &⊕-distL {A = A}{B = C}{C = B} ≡ id
    &⊕-distL-ret =
      funExt λ w → funExt λ { (pA , Sum.inl x) → refl ; (pA , Sum.inr x) → refl}


  &⊕-distL≅ : A & (B ⊕ C) ≅ (A & B) ⊕ (A & C)
  &⊕-distL≅ .fun = &⊕-distL
  &⊕-distL≅ .inv = &⊕-distL⁻
  &⊕-distL≅ .sec = &⊕-distL-sec
  &⊕-distL≅ .ret = &⊕-distL-ret
