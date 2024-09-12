open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Product Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

⊥ : Grammar ℓ-zero
⊥ _ = Empty.⊥

⊥* : Grammar ℓg
⊥* _ = Empty.⊥*

⊥-elim :
  ⊥ ⊢ g
⊥-elim _ = Empty.elim

⊥*-elim :
  ⊥ ⊢ g
⊥*-elim _ = Empty.elim

⊥-η : ∀ (f f' : ⊥ ⊢ g)
  → f ≡ f'
⊥-η _ _ = funExt λ _ → funExt Empty.elim

is-initial : Grammar ℓg → Typeω
is-initial g =
  ∀ {ℓh}{h : Grammar ℓh} → (Σ[ e ∈ g ⊢ h ] (∀ e' → e ≡ e'))

is-initial→propHoms :
  is-initial g →
  ∀ {ℓh}{h : Grammar ℓh} (e e' : g ⊢ h) → e ≡ e'
is-initial→propHoms initg e e' =
  sym (initg .snd e) ∙ initg .snd e'

is-strict-initial : Grammar ℓg → Typeω
is-strict-initial g =
  ∀ {ℓh} {h : Grammar ℓh} (f : h ⊢ g) → isStrongEquivalence h g f

is-initial-⊥ : is-initial ⊥
is-initial-⊥ = ⊥-elim , (λ e → funExt λ x → funExt λ p → Empty.rec p)


open StrongEquivalence

is-initial-⊥&g : (g : Grammar ℓg) → is-initial (⊥ & g)
is-initial-⊥&g g .fst = ⊥-elim ∘g &-π₁
is-initial-⊥&g g .snd e = {!!}
  where
  inl≡inr-⊥ : ⊕-inl ≡ ⊕-inr
  inl≡inr-⊥ =
    is-initial→propHoms is-initial-⊥
      (⊕-inl {g = ⊥}{h = ⊥}) (⊕-inr {g = ⊥}{h = ⊥})

  inl≡inr-⊥&g : ⊕-inl {g = ⊥ & g}{h = ⊥ & g} ≡ ⊕-inr {g = ⊥ & g}{h = ⊥ & g}
  inl≡inr-⊥&g = ?
    -- is-initial→propHoms is-initial-⊥
    --   (⊕-inl {g = ⊥}{h = ⊥}) (⊕-inr {g = ⊥}{h = ⊥})

-- ⊥&g≅⊥ : (g : Grammar ℓg) → StrongEquivalence (⊥ & g) ⊥
-- ⊥&g≅⊥ g .fun = {!!}
-- ⊥&g≅⊥ g .inv = ⊥-elim
-- ⊥&g≅⊥ g .sec = {!!}
-- ⊥&g≅⊥ g .ret = {!!}

-- open isStrongEquivalence

-- is-strict-initial-⊥ : is-strict-initial ⊥
-- is-strict-initial-⊥ f .inv = ⊥-elim
-- is-strict-initial-⊥ f .sec = is-initial-⊥ (f ∘g ⊥-elim) id
-- is-strict-initial-⊥ f .ret = {!!}

-- is-initial-⊥* : ∀ {ℓg} → is-initial (⊥* {ℓg})
-- is-initial-⊥* e e' = funExt (λ x → funExt λ p → Empty.rec (lower p))
