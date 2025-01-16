open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Function (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Product Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Top.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

opaque
  _⇒_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  (g ⇒ h) w = g w → h w

opaque
  unfolding _⇒_ _&_ &-intro
  ⇒-intro :
    g & h ⊢ k →
    g ⊢ h ⇒ k
  ⇒-intro e _ pg = λ ph → e _ (pg , ph)

  ⇒-app :
    (g ⇒ h) & g ⊢ h
  ⇒-app _ (f , pg) = f pg

⇒-intro⁻ :
  g ⊢ h ⇒ k
  → g & h ⊢ k
⇒-intro⁻ f = ⇒-app ∘g &-intro (f ∘g &-π₁) &-π₂

opaque
  unfolding _⇒_ _&_ &-intro ⇒-intro
  ⇒-β :
    (e : g & h ⊢ k) →
    ⇒-intro⁻ (⇒-intro e) ≡ e
  ⇒-β e = refl

  ⇒-η :
    (e : g ⊢ h ⇒ k) →
    ⇒-intro (⇒-intro⁻ e) ≡ e
  ⇒-η e = refl

⇒-mapDom : g ⊢ h → h ⇒ k ⊢ g ⇒ k
⇒-mapDom e = ⇒-intro (⇒-app ∘g id ,&p e)

⇒-comp :
  (g ⇒ h) & (h ⇒ k) ⊢ g ⇒ k
⇒-comp =
  ⇒-intro
    (⇒-app ∘g
    &-par id ⇒-app ∘g
    &-assoc⁻ ∘g
    &-par &-swap id)

term⇒ :
  g ⊢ h →
  ⊤ ⊢ g ⇒ h
term⇒ f = ⇒-intro (f ∘g &-π₂)

id⇒ : ⊤ ⊢ g ⇒ g
id⇒ = term⇒ id

⇐-intro :
  g & h ⊢ k →
  h ⊢ g ⇒ k
⇐-intro e = ⇒-intro (e ∘g &-intro &-π₂ &-π₁)

⇐-intro⁻ :
  h ⊢ g ⇒ k
  → g & h ⊢ k
⇐-intro⁻ f = ⇒-app ∘g &-intro (f ∘g &-π₂) &-π₁
