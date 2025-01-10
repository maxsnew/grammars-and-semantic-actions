open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Bottom.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Product Alphabet
open import Grammar.Function Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Equivalence.Base Alphabet

open import Term.Base Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

is-initial : Grammar ℓg → Typeω
is-initial g =
  ∀ {ℓh}{h : Grammar ℓh} → (Σ[ e ∈ g ⊢ h ] (∀ e' → e ≡ e'))

is-initial→propHoms :
  is-initial g →
  ∀ {ℓh}{h : Grammar ℓh} (e e' : g ⊢ h) → e ≡ e'
is-initial→propHoms initg e e' =
  sym (initg .snd e) ∙ initg .snd e'

-- A grammar is strictly initial if every map into it is a strong equivalence
is-strict-initial : Grammar ℓg → Typeω
is-strict-initial g =
  ∀ {ℓh} {h : Grammar ℓh} (f : h ⊢ g) → isStrongEquivalence h g f

opaque
  unfolding ⊥
  is-initial-⊥ : is-initial ⊥
  is-initial-⊥ = ⊥-elim , (λ e → funExt λ x → funExt λ p → Empty.rec p)

open StrongEquivalence

is-initial-⊥&g : (g : Grammar ℓg) → is-initial (⊥ & g)
is-initial-⊥&g g .fst = ⊥-elim ∘g &-π₁
is-initial-⊥&g g .snd e = p ∙ cong (⊕-elim f e ∘g_) inl≡inr-⊥&g ∙ sym q
  where
  inl≡inr-⊥ : ⊕-inl ≡ ⊕-inr
  inl≡inr-⊥ =
    is-initial→propHoms is-initial-⊥
      (⊕-inl {g = ⊥}{h = ⊥}) (⊕-inr {g = ⊥}{h = ⊥})


  f = is-initial-⊥&g g .fst

  opaque
    unfolding ⊕-inl ⇒-app
    inl≡inr-⊥&g : ⊕-inl {g = ⊥ & g}{h = ⊥ & g} ≡ ⊕-inr {g = ⊥ & g}{h = ⊥ & g}
    inl≡inr-⊥&g i = &⊕-distR ∘g &-par (inl≡inr-⊥ i) id

    p : f ≡ (⊕-elim f e) ∘g ⊕-inl
    p = sym (⊕-βl f e)

    q : e ≡ (⊕-elim f e) ∘g ⊕-inr
    q = sym (⊕-βr f e)

⊥&g≅⊥ : (g : Grammar ℓg) → StrongEquivalence (⊥ & g) ⊥
⊥&g≅⊥ g .fun = is-initial-⊥&g g .fst
⊥&g≅⊥ g .inv = ⊥-elim
⊥&g≅⊥ g .sec = is-initial→propHoms is-initial-⊥ _ _
⊥&g≅⊥ g .ret = is-initial→propHoms (is-initial-⊥&g g) _ _

open isStrongEquivalence

uninhabited : (g : Grammar ℓg) → Type ℓg
uninhabited g = g ⊢ ⊥

opaque
  unfolding _&_ &-intro
  -- Every map into ⊥ is a strong equivalence
  is-strict-initial-⊥ : is-strict-initial ⊥
  is-strict-initial-⊥ f .inv = ⊥-elim
  is-strict-initial-⊥ f .sec = is-initial→propHoms is-initial-⊥ _ _
  is-strict-initial-⊥ {h = h} f .ret =
    cong (_∘g f) (sym q) ∙
    cong ((&-π₂ ∘g ⊥&g≅⊥ h .inv ∘g f) ∘g_) (sym r) ∙
    cong (λ a → &-π₂ ∘g a ∘g (f ,& id)) p
    where
    p : ⊥&g≅⊥ h .inv ∘g f ∘g &-π₂ ≡ id
    p = is-initial→propHoms (is-initial-⊥&g h) _ id

    q : &-π₂ ∘g ⊥&g≅⊥ h .inv ≡ ⊥-elim
    q = is-initial→propHoms is-initial-⊥ _ _

    r : &-π₂ ∘g f ,& id ≡ id
    r = &-β₂ f id

  -- Any g with a map into ⊥ is iso to ⊥, so it is also initial
  g⊢⊥→is-initial :
    uninhabited g →
    is-initial g
  g⊢⊥→is-initial e {h = h} .fst = ⊥-elim {g = h} ∘g e
  g⊢⊥→is-initial e {h = h} .snd e' =
    cong (_∘g e) p ∙ cong (e' ∘g_) (is-strict-initial-⊥ e .ret)
    where
    p : ⊥-elim ≡ e' ∘g ⊥-elim
    p = is-initial→propHoms is-initial-⊥ _ _

opaque
  unfolding ⊥*
  is-initial-⊥* : is-initial (⊥* {ℓg})
  is-initial-⊥* =
    ⊥*-elim , (λ e → funExt λ x → funExt λ p → Empty.rec (lower p))

unambiguous'⊥ : unambiguous' ⊥
unambiguous'⊥ {k = k} e e' !∘e≡!∘e' =
  is-initial→propHoms (g⊢⊥→is-initial e) _ _

unambiguous⊥ : unambiguous ⊥
unambiguous⊥ = unambiguous'→unambiguous unambiguous'⊥
