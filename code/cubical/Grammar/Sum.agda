open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sum as Sum

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
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
  (e₁ : g ⊢ g ⊕ h) →
  (e₂ : h ⊢ g ⊕ h) →
  ⊕-inl ⋆ ⊕-elim e₁ e₂
    ≡
  e₁
⊕-βl e₁ e₂ = refl

⊕-βr :
  (e₁ : g ⊢ g ⊕ h) →
  (e₂ : h ⊢ g ⊕ h) →
  ⊕-inr ⋆ ⊕-elim e₁ e₂
    ≡
  e₂
⊕-βr e₁ e₂ = refl

⊕-η :
  (e : g ⊕ h ⊢ k) →
  (⊕-elim {g = g}{h = k}{k = h}
    (⊕-inl ⋆ e)
    (⊕-inr ⋆ e)
  )
    ≡
    e
⊕-η e i _ (inl x) = e _ (inl x)
⊕-η e i _ (inr x) = e _ (inr x)

⊗-dist-over-⊕ :
  g ⊗ (h ⊕ k) ⊢ (g ⊗ h) ⊕ (g ⊗ k)
⊗-dist-over-⊕ {g = g}{h = h}{k = k} =
  ⊸-intro⁻ {g = h ⊕ k}{h = g}{k = (g ⊗ h) ⊕ (g ⊗ k)}
    (⊕-elim {g = h}{h = g ⊸ ((g ⊗ h) ⊕ (g ⊗ k))}{k = k}
      (⊸-intro {g = g}{h = h}{k = (g ⊗ h) ⊕ (g ⊗ k)} ⊕-inl)
      (⊸-intro {g = g}{h = k}{k = (g ⊗ h) ⊕ (g ⊗ k)} ⊕-inr))
