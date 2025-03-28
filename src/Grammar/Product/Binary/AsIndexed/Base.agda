open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Binary.AsIndexed.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Bool

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX : Level
    A B C D : Grammar ℓA

open StrongEquivalence

&Ind : Grammar ℓA → Grammar ℓA → Bool → Grammar ℓA
&Ind A B true = A
&Ind A B false = B

_&_ : Grammar ℓA → Grammar ℓA → Grammar ℓA
A & B = &ᴰ (&Ind A B)

infixr 27 _&_

module _ {A : Bool → Grammar ℓA} where
  π₁ : &ᴰ A ⊢ A true
  π₁ = π true

  π₂ : &ᴰ A ⊢ A false
  π₂ = π false

  &-intro : B ⊢ A true → B ⊢ A false → B ⊢ &ᴰ A
  &-intro {B = B} e f = &ᴰ-intro &-intro'
    where
    &-intro' : (b : Bool) → B ⊢ A b
    &-intro' true = e
    &-intro' false = f

  _,&_ = &-intro
  infixr 20 _,&_

module _ {A B : Bool → Grammar ℓA} where
  &par : A true ⊢ B true → A false ⊢ B false → &ᴰ A ⊢ &ᴰ B
  &par f f' = (f ∘g π₁) ,& (f' ∘g π₂)

  _,&p_ = &par
  infixr 20 _,&p_

&-β₁ : (e₁ : A ⊢ B) → (e₂ : A ⊢ C) → π₁ {A = &Ind B C} ∘g (e₁ ,& e₂) ≡ e₁
&-β₁ e₁ e₂ = refl

&-β₂ : (e₁ : A ⊢ B) → (e₂ : A ⊢ C) → π₂ {A = &Ind B C} ∘g (e₁ ,& e₂) ≡ e₂
&-β₂ e₁ e₂ = refl

&-η : (e : A ⊢ B & C) → (π₁ ∘g e) ,& (π₂ ∘g e) ≡ e
&-η e = &ᴰ≡ _ _ λ where
  true → refl
  false → refl


module _
  {A B C : Bool → Grammar ℓA}
  (e : A true ⊢ B true) (f : A false ⊢ B false)
  (g : B true ⊢ C true) (h : B false ⊢ C false) where
  &par∘ : (&par {A = B} {B = C} g h) ∘g (&par {A = A} e f) ≡ (g ∘g e) ,&p (h ∘g f)
  &par∘ = &ᴰ≡ _ _ λ where
    true → refl
    false → refl

id&_ : B ⊢ C → A & B ⊢ A & C
id& f = π₁ ,& (f ∘g π₂)

&-swap : A & B ⊢ B & A
&-swap = π₂ ,& π₁

&-Δ : A ⊢ A & A
&-Δ = id ,& id

module _
  {A B : Grammar ℓA}
  where
  &-swap-invol : &-swap ∘g &-swap {A = A}{B = B} ≡ id
  &-swap-invol = &ᴰ≡ _ _ λ where
    true → refl
    false → refl

&-assoc : A & (B & C) ⊢ (A & B) & C
&-assoc = (π₁ ,& (π₁ ∘g π₂)) ,& (π₂ ∘g π₂)

&-assoc⁻ : (A & B) & C ⊢ A & (B & C)
&-assoc⁻ = (π₁ ∘g π₁) ,& ((π₂ ∘g π₁) ,& π₂)

&-par : A ⊢ B → C ⊢ D → A & C ⊢ B & D
&-par e e' = (e ∘g π₁) ,& (e' ∘g π₂)

module _ {A B C D : Grammar ℓA}
  (A≅B : A ≅ B) (C≅D : C ≅ D)
  where

  private
    the-fun : A & C ⊢ B & D
    the-fun = A≅B .fun ,&p C≅D .fun

    the-inv : B & D ⊢ A & C
    the-inv = A≅B .inv ,&p C≅D .inv

    the-sec : the-fun ∘g the-inv ≡ id
    the-sec = &ᴰ≡ _ _ λ where
      true → cong (_∘g π₁) (A≅B .sec)
      false → cong (_∘g π₂) (C≅D .sec)

    the-ret : the-inv ∘g the-fun ≡ id
    the-ret = &ᴰ≡ _ _ λ where
      true → cong (_∘g π₁) (A≅B .ret)
      false → cong (_∘g π₂) (C≅D .ret)

  &≅ : (A & C) ≅ (B & D)
  &≅ .fun = the-fun
  &≅ .inv = the-inv
  &≅ .sec = the-sec
  &≅ .ret = the-ret

module _ {A B : Grammar ℓA} where
  &-swap≅ : A & B ≅ B & A
  &-swap≅ .fun = &-swap
  &-swap≅ .inv = &-swap
  &-swap≅ .sec = &-swap-invol
  &-swap≅ .ret = &-swap-invol
