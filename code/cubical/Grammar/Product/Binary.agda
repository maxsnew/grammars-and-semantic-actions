open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Binary (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Dependent Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

module InductiveBinaryProduct where
  _&_ : Grammar ℓA → Grammar ℓA → Grammar ℓA
  A & B = &ᴰ {X = Bool} λ where
    true → A
    false → B

  infixr 27 _&_

  &-intro :
    A ⊢ B →
    A ⊢ C →
    A ⊢ B & C
  &-intro e f = &ᴰ-in λ where
    true → e
    false → f

  &-π₁ :
    A & B ⊢ A
  &-π₁ = &ᴰ-π true

  &-π₂ :
    A & B ⊢ B
  &-π₂ = &ᴰ-π false

  &-β₁ :
    (e₁ : A ⊢ B) →
    (e₂ : A ⊢ C) →
    &-π₁ ∘g (&-intro e₁ e₂)
      ≡
    e₁
  &-β₁ e₁ e₂ = refl

  &-β₂ :
    (e₁ : A ⊢ B) →
    (e₂ : A ⊢ C) →
    &-π₂ ∘g (&-intro e₁ e₂)
      ≡
    e₂
  &-β₂ e₁ e₂ = refl

  &-η :
    (e : A ⊢ B & C) →
    (&-intro {A = A}{B = B}{C = C}
      (&-π₁ ∘g e)
      (&-π₂ ∘g e))
    ≡
    e
  &-η e = &ᴰ≡ _ _ λ where
    true → refl
    false → refl

  _,&_ = &-intro
  infixr 20 _,&_

  &par : A ⊢ B → C ⊢ D → A & C ⊢ B & D
  &par f f' = (f ∘g &-π₁) ,& (f' ∘g &-π₂)

  _,&p_ = &par
  infixr 20 _,&p_

  id&_ : B ⊢ C → A & B ⊢ A & C
  id& f = &-π₁ ,& (f ∘g &-π₂)

  &-swap :
    A & B ⊢ B & A
  &-swap = &-intro &-π₂ &-π₁

  &-Δ : A ⊢ A & A
  &-Δ = id ,& id

  module _
    {A B : Grammar ℓA}
    where
    &-swap-invol : &-swap ∘g &-swap {A = A}{B = B} ≡ id
    &-swap-invol = &ᴰ≡ _ _ λ where
      true → refl
      false → refl

  &-assoc :
    A & (B & C) ⊢ (A & B) & C
  &-assoc = &-intro (&-intro &-π₁ (&-π₁ ∘g &-π₂)) (&-π₂ ∘g &-π₂)

  &-assoc⁻ :
    (A & B) & C ⊢ A & (B & C)
  &-assoc⁻ = &-intro (&-π₁ ∘g &-π₁) (&-intro (&-π₂ ∘g &-π₁) &-π₂)

  &-par :
    A ⊢ B → C ⊢ D →
    A & C ⊢ B & D
  &-par e e' = &-intro (e ∘g &-π₁) (e' ∘g &-π₂)

  module _
    {A B C D : Grammar ℓA}
    (A≅B : A ≅ B)
    (C≅D : C ≅ D)
    where

    private
      the-fun : A & C ⊢ B & D
      the-fun = A≅B .fun ,&p C≅D .fun

      the-inv : B & D ⊢ A & C
      the-inv = A≅B .inv ,&p C≅D .inv

      the-sec : the-fun ∘g the-inv ≡ id
      the-sec = &ᴰ≡ _ _ λ where
        true → cong (_∘g &-π₁) (A≅B .sec)
        false → cong (_∘g &-π₂) (C≅D .sec)

      the-ret : the-inv ∘g the-fun ≡ id
      the-ret = &ᴰ≡ _ _ λ where
        true → cong (_∘g &-π₁) (A≅B .ret)
        false → cong (_∘g &-π₂) (C≅D .ret)

    &≅ : (A & C) ≅ (B & D)
    &≅ .fun = the-fun
    &≅ .inv = the-inv
    &≅ .sec = the-sec
    &≅ .ret = the-ret

  module _
    {A B : Grammar ℓA}
    where
    &-swap≅ : A & B ≅ B & A
    &-swap≅ .fun = &-swap
    &-swap≅ .inv = &-swap
    &-swap≅ .sec = &-swap-invol
    &-swap≅ .ret = &-swap-invol
