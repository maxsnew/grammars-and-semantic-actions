open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Product (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

_&_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g & h) w = g w × h w

infixr 5 _&_

&-intro :
  g ⊢ h →
  g ⊢ k →
  g ⊢ h & k
&-intro e e' _ p =
  e _ p , e' _ p

_,&_ = &-intro
infixr 20 _,&_

&-π₁ :
  g & h ⊢ g
&-π₁ _ p = p .fst

&-π₂ :
  g & h ⊢ h
&-π₂ _ p = p .snd

&par : g ⊢ h → k ⊢ l → g & k ⊢ h & l
&par f f' = (f ∘g &-π₁) ,& (f' ∘g &-π₂)

_,&p_ = &par
infixr 20 _,&p_

id&_ : h ⊢ k → g & h ⊢ g & k
id& f = &-π₁ ,& (f ∘g &-π₂)

&-β₁ :
  (e₁ : g ⊢ h) →
  (e₂ : g ⊢ k) →
  (&-intro e₁ e₂) ⋆ &-π₁
    ≡
  e₁
&-β₁ e₁ e₂ = refl

&-β₂ :
  (e₁ : g ⊢ h) →
  (e₂ : g ⊢ k) →
  (&-intro e₁ e₂) ⋆ &-π₂
    ≡
  e₂
&-β₂ e₁ e₂ = refl

&-η :
  (e : g ⊢ h & k) →
  (&-intro {g = g}{h = h}{k = k}
    (e ⋆ &-π₁)
    (e ⋆ &-π₂))
  ≡
  e
&-η e = refl
