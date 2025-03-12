open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Function.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Product.Binary.Cartesian.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Top.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

opaque
  _⇒_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
  (A ⇒ B) w = A w → B w

opaque
  unfolding _⇒_ _&_ &-intro
  ⇒-intro :
    A & B ⊢ C →
    A ⊢ B ⇒ C
  ⇒-intro e _ pA = λ pB → e _ (pA , pB)

  ⇒-app :
    (A ⇒ B) & A ⊢ B
  ⇒-app _ (f , pA) = f pA

⇒-intro⁻ :
  A ⊢ B ⇒ C
  → A & B ⊢ C
⇒-intro⁻ f = ⇒-app ∘g &-intro (f ∘g π₁) π₂

opaque
  unfolding _⇒_ _&_ &-intro ⇒-intro π₁
  ⇒-β :
    (e : A & B ⊢ C) →
    ⇒-intro⁻ (⇒-intro e) ≡ e
  ⇒-β e = refl

  ⇒-η :
    (e : A ⊢ B ⇒ C) →
    ⇒-intro (⇒-intro⁻ e) ≡ e
  ⇒-η e = refl

⇒-mapDom : A ⊢ B → B ⇒ C ⊢ A ⇒ C
⇒-mapDom e = ⇒-intro (⇒-app ∘g id ,&p e)

⇒-comp :
  (A ⇒ B) & (B ⇒ C) ⊢ A ⇒ C
⇒-comp =
  ⇒-intro
    (⇒-app ∘g
    &-par id ⇒-app ∘g
    &-assoc⁻ ∘g
    &-par &-swap id)

term⇒ :
  A ⊢ B →
  ⊤ ⊢ A ⇒ B
term⇒ f = ⇒-intro (f ∘g π₂)

id⇒ : ⊤ ⊢ A ⇒ A
id⇒ = term⇒ id

⇐-intro :
  A & B ⊢ C →
  B ⊢ A ⇒ C
⇐-intro e = ⇒-intro (e ∘g &-intro π₂ π₁)

⇐-intro⁻ :
  B ⊢ A ⇒ C
  → A & B ⊢ C
⇐-intro⁻ f = ⇒-app ∘g &-intro (f ∘g π₂) π₁
