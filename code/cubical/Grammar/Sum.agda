{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sum as Sum

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

_⊕_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g ⊕ h) w = g w ⊎ h w

infixr 5 _⊕_

⊕-inl :
  g ⊢ g ⊕ h
⊕-inl _ p = inl p

⊕-inr :
  g ⊢ h ⊕ g
⊕-inr _ p = inr p

⊕-elim :
  g ⊢ h →
  k ⊢ h →
  g ⊕ k ⊢ h
⊕-elim eg eh _ p =
  Sum.elim
    (λ pg → eg _ pg)
    (λ ph → eh _ ph)
    p

⊕≡ :
  (f f' : g ⊕ k ⊢ h)
  → (f ∘g ⊕-inl ≡ f' ∘g ⊕-inl)
  → (f ∘g ⊕-inr ≡ f' ∘g ⊕-inr)
  → f ≡ f'
⊕≡ f f' f≡f'inl f≡f'inr = funExt λ w → funExt λ
  { (inl x) → funExt⁻ (funExt⁻ f≡f'inl _) x
  ; (inr x) → funExt⁻ (funExt⁻ f≡f'inr _) x }

⊕-βl :
  (e₁ : g ⊢ k) →
  (e₂ : h ⊢ k) →
  ⊕-inl ⋆ ⊕-elim e₁ e₂
    ≡
  e₁
⊕-βl e₁ e₂ = refl

⊕-βr :
  (e₁ : g ⊢ k) →
  (e₂ : h ⊢ k) →
  ⊕-inr ⋆ ⊕-elim e₁ e₂
    ≡
  e₂
⊕-βr e₁ e₂ = refl

⊕-η :
  (e : g ⊕ h ⊢ k) →
  (⊕-elim {g = g}{h = k}{k = h}
    (e ∘g ⊕-inl)
    (e ∘g ⊕-inr)
  )
    ≡
    e
⊕-η e i _ (inl x) = e _ (inl x)
⊕-η e i _ (inr x) = e _ (inr x)

⊗⊕-distL :
  g ⊗ (h ⊕ k) ⊢ (g ⊗ h) ⊕ (g ⊗ k)
⊗⊕-distL {g = g}{h = h}{k = k} =
  ⊸-intro⁻ {g = h ⊕ k}{h = g}{k = (g ⊗ h) ⊕ (g ⊗ k)}
    (⊕-elim {g = h}{h = g ⊸ ((g ⊗ h) ⊕ (g ⊗ k))}{k = k}
      (⊸-intro {g = g}{h = h}{k = (g ⊗ h) ⊕ (g ⊗ k)} ⊕-inl)
      (⊸-intro {g = g}{h = k}{k = (g ⊗ h) ⊕ (g ⊗ k)} ⊕-inr))

⊗⊕-distR :
  (g ⊕ h) ⊗ k ⊢ (g ⊗ k) ⊕ (h ⊗ k)
⊗⊕-distR {g = g}{h = h}{k = k} =
  ⟜-intro⁻
    (⊕-elim (⟜-intro (⊕-inl {h = h ⊗ k}))
    (⟜-intro (⊕-inr {h = g ⊗ k})))

&⊕-distR :
  (g ⊕ h) & k ⊢ (g & k) ⊕ (h & k)
&⊕-distR =
  ⇒-intro⁻
    (⊕-elim
      (⇒-intro ⊕-inl)
      (⇒-intro ⊕-inr))

&⊕-distR⁻ :
 (g & h) ⊕ (k & h) ⊢ (g ⊕ k) & h
&⊕-distR⁻ = ⊕-elim (&-par ⊕-inl id) (&-par ⊕-inr id)

open StrongEquivalence

&⊕-distR≅ :
  StrongEquivalence
    ((g ⊕ k) & h)
    ((g & h) ⊕ (k & h))
&⊕-distR≅ .fun = &⊕-distR
&⊕-distR≅ .inv = &⊕-distR⁻
&⊕-distR≅ .sec =
  {!!}
  -- ⇒-app ∘g &-intro (⊕-elim (⇒-intro ⊕-inl) (⇒-intro ⊕-inr) ∘g &-π₁) &-π₂ ∘g
  -- ⊕-elim (&-par ⊕-inl id) (&-par ⊕-inr id)
  --   ≡⟨ (λ i → ⇒-app ∘g &-intro (⊕-η (⇒-intro {!!}) i ∘g &-π₁) &-π₂ ∘g
  --             ⊕-elim (&-par ⊕-inl id) (&-par ⊕-inr id)) ⟩
  -- {!!}

  --   ≡⟨ {!!} ⟩
  -- id
  -- ∎
&⊕-distR≅ .ret = {!!}


&⊕-distL :
  g & (h ⊕ k) ⊢ (g & h) ⊕ (g & k)
&⊕-distL =
  ⇒-intro⁻
    (⊕-elim
      (⇒-intro (⊕-inl ∘g &-swap))
      (⇒-intro (⊕-inr ∘g &-swap))) ∘g
  &-swap

&⊕-distL⁻ :
 (g & h) ⊕ (g & k) ⊢ g & (h ⊕ k)
&⊕-distL⁻ = ⊕-elim (&-par id ⊕-inl) (&-par id ⊕-inr)

&⊕-distL≅ :
  StrongEquivalence
    (g & (h ⊕ k))
    ((g & h) ⊕ (g & k))
&⊕-distL≅ .fun = &⊕-distL
&⊕-distL≅ .inv = &⊕-distL⁻
&⊕-distL≅ .sec = {!!}
&⊕-distL≅ .ret = {!!}
