{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude hiding (Lift ; lift ; lower)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module @0 Grammar.Bottom.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Erased.Data.Empty.Base as Empty hiding (⊥ ; ⊥*)
open import Erased.Lift.Base
import Erased.Data.Sum.Base as Sum

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Bottom.Base Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.Base Alphabet isSetAlphabet
open import Grammar.LinearFunction Alphabet isSetAlphabet
open import Grammar.Function Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Distributivity Alphabet isSetAlphabet

open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

@0 is-initial : Grammar ℓA → Typeω
is-initial A =
  ∀ {ℓB}{B : Grammar ℓB} → (Σ[ e ∈ A ⊢ B ] (∀ e' → e ≡ e'))

@0 is-initial→propHoms :
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
  @0 is-initial-⊥ : is-initial ⊥
  is-initial-⊥ = ⊥-elim , (λ e → funExt λ x → funExt λ p → Empty.rec p)

open StrongEquivalence

@0 is-initial-⊥&A : (A : Grammar ℓA) → is-initial (⊥ & A)
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
    @0 inl≡inr-⊥&A : inl {A = ⊥ & A}{B = ⊥ & A} ≡ inr {A = ⊥ & A}{B = ⊥ & A}
    inl≡inr-⊥&A i = &⊕-distR ∘g &-par (inl≡inr-⊥ i) id

    @0 p : f ≡ (⊕-elim f e) ∘g inl
    p = sym (⊕-βl f e)

    @0 q : e ≡ (⊕-elim f e) ∘g inr
    q = sym (⊕-βr f e)

@0 ⊥&A≅⊥ : (A : Grammar ℓA) → (⊥ & A) ≅ ⊥
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
  @0 A⊢⊥→is-initial : uninhabited A → is-initial A
  A⊢⊥→is-initial e {B = B} .fst = ⊥-elim {A = B} ∘g e
  A⊢⊥→is-initial e {B = B} .snd e' =
    cong (_∘g e) p ∙ cong (e' ∘g_) (is-strict-initial-⊥ e .ret)
    where
    p : ⊥-elim ≡ e' ∘g ⊥-elim
    p = is-initial→propHoms is-initial-⊥ _ _

@0 uninhabited→initial : uninhabited A → is-initial A
uninhabited→initial = A⊢⊥→is-initial

opaque
  unfolding ⊥*
  @0 is-initial-⊥* : is-initial (⊥* {ℓA})
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

@0 unambiguous'⊥ : unambiguous' ⊥
unambiguous'⊥ {C = C} e e' !∘e≡!∘e' =
  is-initial→propHoms (A⊢⊥→is-initial e) _ _

@0 unambiguous⊥ : unambiguous ⊥
unambiguous⊥ = unambiguous'→unambiguous unambiguous'⊥

@0 isProp-uninhabited : ∀ {A : Grammar ℓA} → isProp (uninhabited A)
isProp-uninhabited = unambiguous⊥

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
      @0 the-ret : ⊥⊕≅ .inv ∘g ⊥⊕≅ .fun ≡ id
      the-ret = funExt λ w → funExt λ {
        (Sum.inr x) → refl
        }
