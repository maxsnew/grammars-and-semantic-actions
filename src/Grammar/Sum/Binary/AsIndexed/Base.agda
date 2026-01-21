open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Sum.Binary.AsIndexed.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Bool as Bool using (Bool ; true ; false)

open import Grammar.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓ ℓ' : Level
    A B C D : Grammar ℓA

⊕Ind : Grammar ℓA → Grammar ℓA → Bool → Grammar ℓA
⊕Ind A B true = A
⊕Ind A B false = B

_⊕_ : Grammar ℓA → Grammar ℓA → Grammar ℓA
A ⊕ B = ⊕ᴰ (⊕Ind A B)

infixr 18 _⊕_

module _ {A : Bool → Grammar ℓA} where
  inl : A true ⊢ ⊕ᴰ A
  inl = σ true

  inr : A false ⊢ ⊕ᴰ A
  inr = σ false

  ⊕-elim : A true ⊢ B → A false ⊢ B → ⊕ᴰ A ⊢ B
  ⊕-elim {B = B} e f = ⊕ᴰ-elim (Bool.elim e f)

⊕-βl : (e₁ : A ⊢ C) → (e₂ : B ⊢ C) →
  ⊕-elim {A = ⊕Ind _ _} e₁ e₂ ∘g inl ≡ e₁
⊕-βl e₁ e₂ = refl

⊕-βr : (e₁ : A ⊢ C) → (e₂ : B ⊢ C) →
  ⊕-elim {A = ⊕Ind _ _} e₁ e₂ ∘g inr ≡ e₂
⊕-βr e₁ e₂ = refl

⊕-η : (e : A ⊕ B ⊢ C) →
  ⊕-elim (e ∘g inl) (e ∘g inr) ≡ e
⊕-η e = ⊕ᴰ≡ _ _ λ where
  true → refl
  false → refl

_,⊕p_ : A ⊢ B → C ⊢ D →
  A ⊕ C ⊢ B ⊕ D
e ,⊕p f = ⊕-elim (inl ∘g e) (inr ∘g f)

⊕-swap : A ⊕ B ⊢ B ⊕ A
⊕-swap = ⊕-elim inr inl

⊕-swap-invol : ⊕-swap ∘g ⊕-swap {A = A}{B = B} ≡ id
⊕-swap-invol = ⊕ᴰ≡ _ _ λ where
  true → refl
  false → refl

open StrongEquivalence

module _ {A B C D : Grammar ℓA}
  (A≅B : A ≅ B) (C≅D : C ≅ D) where

  private
    the-fun : A ⊕ C ⊢ B ⊕ D
    the-fun = A≅B .fun ,⊕p C≅D .fun

    the-inv : B ⊕ D ⊢ A ⊕ C
    the-inv = A≅B .inv ,⊕p C≅D .inv

    the-sec : the-fun ∘g the-inv ≡ id
    the-sec = ⊕ᴰ≡ _ _ λ where
      true → (cong (inl ∘g_) (A≅B .sec))
      false → (cong (inr ∘g_) (C≅D .sec))

    the-ret : the-inv ∘g the-fun ≡ id
    the-ret = ⊕ᴰ≡ _ _ λ where
      true → (cong (inl ∘g_) (A≅B .ret))
      false → (cong (inr ∘g_) (C≅D .ret))

  ⊕≅ : (A ⊕ C) ≅ (B ⊕ D)
  ⊕≅ .fun = the-fun
  ⊕≅ .inv = the-inv
  ⊕≅ .sec = the-sec
  ⊕≅ .ret = the-ret

module _ {A B : Grammar ℓA} where
  ⊕-swap≅ : (A ⊕ B) ≅ (B ⊕ A)
  ⊕-swap≅ .fun = ⊕-swap
  ⊕-swap≅ .inv = ⊕-swap
  ⊕-swap≅ .sec = ⊕-swap-invol
  ⊕-swap≅ .ret = ⊕-swap-invol

module _
  {A B C : Grammar ℓA}
  where

  ⊕-assoc : (A ⊕ B) ⊕ C ⊢ A ⊕ (B ⊕ C)
  ⊕-assoc = ⊕-elim (⊕-elim inl (inr ∘g inl)) (inr ∘g inr)

  ⊕-assoc⁻ : A ⊕ (B ⊕ C) ⊢ (A ⊕ B) ⊕ C
  ⊕-assoc⁻ = ⊕-elim (inl ∘g inl) (⊕-elim (inl ∘g inr) inr)

  private
    the-sec : ⊕-assoc ∘g ⊕-assoc⁻ ≡ id
    the-sec = ⊕ᴰ≡ _ _ λ where
      true → refl
      false → ⊕ᴰ≡ _ _ λ where
        true → refl
        false → refl

    the-ret : ⊕-assoc⁻ ∘g ⊕-assoc ≡ id
    the-ret = ⊕ᴰ≡ _ _ λ where
      false → refl
      true → ⊕ᴰ≡ _ _ λ where
        true → refl
        false → refl

  ⊕-assoc≅ : (A ⊕ B) ⊕ C ≅ A ⊕ (B ⊕ C)
  ⊕-assoc≅ .fun = ⊕-assoc
  ⊕-assoc≅ .inv = ⊕-assoc⁻
  ⊕-assoc≅ .sec = the-sec
  ⊕-assoc≅ .ret = the-ret
