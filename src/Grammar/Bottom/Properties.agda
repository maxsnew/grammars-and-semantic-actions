open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Bottom.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)
import Cubical.Data.Sum as Sum

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Function Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Distributivity Alphabet

open import Term.Base Alphabet

private
  variable
    ℓ ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

is-initial : Grammar ℓA → Typeω
is-initial A =
  ∀ {ℓB}{B : Grammar ℓB} → (Σ[ e ∈ A ⊢ B ] (∀ e' → e ≡ e'))

is-initial→propHoms :
  is-initial A →
  ∀ {ℓB}{B : Grammar ℓB} (e e' : A ⊢ B) → e ≡ e'
is-initial→propHoms initA e e' =
  sym (initA .snd e) ∙ initA .snd e'

-- A grammar is strictly initial if every map into it is a strong equivalence
is-strict-initial : Grammar ℓA → Typeω
is-strict-initial A =
  ∀ {ℓB} {B : Grammar ℓB} (f : B ⊢ A) → isStrongEquivalence B A f

opaque
  unfolding ⊥
  is-initial-⊥ : is-initial ⊥
  is-initial-⊥ = ⊥-elim , (λ e → funExt λ x → funExt λ p → Empty.rec p)

open StrongEquivalence

is-initial-⊥&A : (A : Grammar ℓA) → is-initial (⊥ & A)
is-initial-⊥&A A .fst = ⊥-elim ∘g π₁
is-initial-⊥&A A .snd e = p ∙ cong (⊕-elim f e ∘g_) inl≡inr-⊥&A ∙ sym q
  where
  inl≡inr-⊥ : inl ≡ inr
  inl≡inr-⊥ =
    is-initial→propHoms is-initial-⊥
      (inl {A = ⊥}{B = ⊥}) (inr {A = ⊥}{B = ⊥})


  f = is-initial-⊥&A A .fst

  opaque
    unfolding inl ⇒-app π₁
    inl≡inr-⊥&A : inl {A = ⊥ & A}{B = ⊥ & A} ≡ inr {A = ⊥ & A}{B = ⊥ & A}
    inl≡inr-⊥&A i = &⊕-distR ∘g &-par (inl≡inr-⊥ i) id

    p : f ≡ (⊕-elim f e) ∘g inl
    p = sym (⊕-βl f e)

    q : e ≡ (⊕-elim f e) ∘g inr
    q = sym (⊕-βr f e)

⊥&A≅⊥ : (A : Grammar ℓA) → (⊥ & A) ≅ ⊥
⊥&A≅⊥ A .fun = is-initial-⊥&A A .fst
⊥&A≅⊥ A .inv = ⊥-elim
⊥&A≅⊥ A .sec = is-initial→propHoms is-initial-⊥ _ _
⊥&A≅⊥ A .ret = is-initial→propHoms (is-initial-⊥&A A) _ _

open isStrongEquivalence

uninhabited : (A : Grammar ℓA) → Type ℓA
uninhabited A = A ⊢ ⊥

opaque
  unfolding _&_ &-intro π₁
  -- Every map into ⊥ is a strong equivalence
  is-strict-initial-⊥ : is-strict-initial ⊥
  is-strict-initial-⊥ f .inv = ⊥-elim
  is-strict-initial-⊥ f .sec = is-initial→propHoms is-initial-⊥ _ _
  is-strict-initial-⊥ {B = B} f .ret =
    cong (_∘g f) (sym q) ∙
    cong ((π₂ ∘g ⊥&A≅⊥ B .inv ∘g f) ∘g_) (sym r) ∙
    cong (λ a → π₂ ∘g a ∘g (f ,& id)) p
    where
    p : ⊥&A≅⊥ B .inv ∘g f ∘g π₂ ≡ id
    p = is-initial→propHoms (is-initial-⊥&A B) _ id

    q : π₂ ∘g ⊥&A≅⊥ B .inv ≡ ⊥-elim
    q = is-initial→propHoms is-initial-⊥ _ _

    r : π₂ ∘g f ,& id ≡ id
    r = &-β₂ f id

  -- Any g with a map into ⊥ is iso to ⊥, so it is also initial
  A⊢⊥→is-initial :
    uninhabited A →
    is-initial A
  A⊢⊥→is-initial e {B = B} .fst = ⊥-elim {A = B} ∘g e
  A⊢⊥→is-initial e {B = B} .snd e' =
    cong (_∘g e) p ∙ cong (e' ∘g_) (is-strict-initial-⊥ e .ret)
    where
    p : ⊥-elim ≡ e' ∘g ⊥-elim
    p = is-initial→propHoms is-initial-⊥ _ _

uninhabited→initial : uninhabited A → is-initial A
uninhabited→initial = A⊢⊥→is-initial

opaque
  unfolding ⊥*
  is-initial-⊥* : is-initial (⊥* {ℓA})
  is-initial-⊥* =
    ⊥*-elim , (λ e → funExt λ x → funExt λ p → Empty.rec (lower p))

uninhabited→≅⊥ :
  A ⊢ ⊥ →
  A ≅ ⊥
uninhabited→≅⊥ e =
  mkStrEq e (x .inv) (x .sec) (x .ret)
  where
  x : isStrongEquivalence _ _ e
  x = is-strict-initial-⊥ e

unambiguous'⊥ : unambiguous' ⊥
unambiguous'⊥ {C = C} e e' !∘e≡!∘e' =
  is-initial→propHoms (A⊢⊥→is-initial e) _ _

unambiguous⊥ : unambiguous ⊥
unambiguous⊥ = unambiguous'→unambiguous unambiguous'⊥

isProp-uninhabited : ∀ {A : Grammar ℓA} → isProp (uninhabited A)
isProp-uninhabited = unambiguous⊥

uninhabited→PropHoms : uninhabited A → ∀ {e e' : A ⊢ B} → e ≡ e'
uninhabited→PropHoms uninh = is-initial→propHoms (uninhabited→initial uninh) _ _

module _ (A : Grammar ℓA) where
  open StrongEquivalence
  ⊥⊕≅ : (⊥ ⊕ A) ≅ A
  ⊥⊕≅ .fun = ⊕-elim ⊥-elim id
  ⊥⊕≅ .inv = inr
  ⊥⊕≅ .sec = ⊕-βr ⊥-elim id
  ⊥⊕≅ .ret = the-ret
    where
    opaque
      unfolding ⊕-elim ⊥
      the-ret : ⊥⊕≅ .inv ∘g ⊥⊕≅ .fun ≡ id
      the-ret = funExt λ w → funExt λ {
        (Sum.inr x) → refl
        }

⊗⊥ : A ⊗ ⊥ ⊢ ⊥
⊗⊥ = ⟜-app ∘g id ,⊗ ⊥-elim

⊥⊗ : ⊥ ⊗ A ⊢ ⊥
⊥⊗ = ⊸-app ∘g ⊥-elim ,⊗ id

⊗⊥* : A ⊗ ⊥* {ℓ} ⊢ B
⊗⊥* = ⟜-app ∘g id ,⊗ ⊥*-elim

⊥*⊗ : ⊥* {ℓ} ⊗ A ⊢ B
⊥*⊗ = ⊸-app ∘g ⊥*-elim ,⊗ id
