open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

opaque
  _&_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  (g & h) w = g w × h w

infixr 5 _&_

opaque
  unfolding _&_
  &-intro :
    g ⊢ h →
    g ⊢ k →
    g ⊢ h & k
  &-intro e e' _ p =
    e _ p , e' _ p

  &-π₁ :
    g & h ⊢ g
  &-π₁ _ p = p .fst

  &-π₂ :
    g & h ⊢ h
  &-π₂ _ p = p .snd

  &-β₁ :
    (e₁ : g ⊢ h) →
    (e₂ : g ⊢ k) →
    &-π₁ ∘g (&-intro e₁ e₂)
      ≡
    e₁
  &-β₁ e₁ e₂ = refl

  &-β₂ :
    (e₁ : g ⊢ h) →
    (e₂ : g ⊢ k) →
    &-π₂ ∘g (&-intro e₁ e₂)
      ≡
    e₂
  &-β₂ e₁ e₂ = refl

  &-η :
    (e : g ⊢ h & k) →
    (&-intro {g = g}{h = h}{k = k}
      (&-π₁ ∘g e)
      (&-π₂ ∘g e))
    ≡
    e
  &-η e = refl

&-swap :
  g & h ⊢ h & g
&-swap = &-intro &-π₂ &-π₁

&-assoc :
  g & (h & k) ⊢ (g & h) & k
&-assoc = &-intro (&-intro &-π₁ (&-π₁ ∘g &-π₂)) (&-π₂ ∘g &-π₂)

&-assoc⁻ :
  (g & h) & k ⊢ g & (h & k)
&-assoc⁻ = &-intro (&-π₁ ∘g &-π₁) (&-intro (&-π₂ ∘g &-π₁) &-π₂)

&-par :
  g ⊢ h → k ⊢ l →
  g & k ⊢ h & l
&-par e e' = &-intro (e ∘g &-π₁) (e' ∘g &-π₂)

⊗&-distL :
  g ⊗ (h & k) ⊢ (g ⊗ h) & (g ⊗ k)
⊗&-distL = &-intro (⊗-intro id &-π₁) (⊗-intro id &-π₂)

⊗&-distR :
  (g & h) ⊗ k ⊢ (g ⊗ k) & (h ⊗ k)
⊗&-distR = &-intro (⊗-intro &-π₁ id) (⊗-intro &-π₂ id)

_,&_ = &-intro
infixr 20 _,&_
