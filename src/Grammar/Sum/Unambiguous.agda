open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Unambiguous (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
open import Cubical.Data.Maybe hiding (rec)

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar.Base Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Distributivity Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Top Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX ℓY : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

module _
  {X : Type ℓX} {A : X → Grammar ℓA}
  (isSetX : isSet X)
  where

  opaque
    isMono-σ : (x : X) → isMono (σ {A = A} x)
    isMono-σ x e e' σe=σe' =
      funExt λ w → funExt λ p →
        sym (transportRefl (e w p)) ∙
        Σ-contractFst (refl , (isSetX _ _ _)) .fst
          (PathΣ→ΣPathTransport _ _ (funExt⁻ (funExt⁻ σe=σe' w) p))

  unambiguous'⊕ᴰ :
    unambiguous' (⊕[ x ∈ X ] A x) →
      (x : X)  → unambiguous' (A x)
  unambiguous'⊕ᴰ unambig⊕ x f f' !≡ =
    isMono-σ x f f'
      (unambig⊕ (σ x ∘g f) (σ x ∘g f')
        (unambiguous⊤ _ _ ∙ !≡ ∙ sym (unambiguous⊤ _ _)))

  unambiguous⊕ᴰ : unambiguous (⊕[ x ∈ X ] A x) → (x : X) →
    unambiguous (A x)
  unambiguous⊕ᴰ unambig⊕ x =
    unambiguous'→unambiguous
      (unambiguous'⊕ᴰ (unambiguous→unambiguous' unambig⊕) x)

  module _
    (unambig⊕ : unambiguous (⊕[ x ∈ X ] A x))
    where
    opaque
      unfolding _&_ ⊥
      equalizer→⊥ :
        (x y : X) →
        (x ≡ y → Empty.⊥) →
        equalizer (σ {A = A} x ∘g π₁) (σ y ∘g π₂) ⊢ ⊥
      equalizer→⊥ x y x≠y w p =
        x≠y (cong fst (funExt⁻ (funExt⁻ (eq-π-pf (σ {A = A} x ∘g π₁) (σ y ∘g π₂)) w) p))

    hasDisjointSummands⊕ᴰ : disjointSummands⊕ᴰ A
    hasDisjointSummands⊕ᴰ x y x≠y =
      equalizer→⊥ x y x≠y
      ∘g eq-intro {A = A x & A y}{B = ⊕[ x ∈ X ] A x}
        (σ x ∘g π₁) (σ y ∘g π₂) id
        (unambig⊕ (σ x ∘g π₁) (σ y ∘g π₂))

-- Converse: the indexed coproduct of pairwise disjoint, unambiguous
-- grammars (indexed by a discrete type) is unambiguous.
open StrongEquivalence

module _
  {X : Type ℓX}
  {A : X → Grammar ℓA}
  (discX : Discrete X)
  (unambig-A : ∀ x → unambiguous (A x))
  (dis-A : disjointSummands⊕ᴰ A)
  where

  private
    case-≡ : ∀ x y → x ≡ y
      → σ {A = A} x ∘g π₁ {A = A x} {B = A y} ≡ σ y ∘g π₂
    case-≡ x y p =
      J (λ y' _ → σ {A = A} x ∘g π₁ {A = A x} {B = A y'} ≡ σ y' ∘g π₂)
        (cong (σ x ∘g_) (unambig-A x π₁ π₂))
        p

    case-≢ : ∀ x y → (x ≡ y → Empty.⊥)
      → σ {A = A} x ∘g π₁ {A = A x} {B = A y} ≡ σ y ∘g π₂
    case-≢ x y x≢y =
      is-initial→propHoms (uninhabited→initial (dis-A x y x≢y)) _ _

    cases : ∀ x y → σ {A = A} x ∘g π₁ {A = A x} {B = A y} ≡ σ y ∘g π₂
    cases x y with discX x y
    ... | yes p = case-≡ x y p
    ... | no ¬p = case-≢ x y ¬p

  opaque
    unfolding _&_ &-intro π₁
    unambiguous⊕ᴰ-from-disjoint : unambiguous (⊕ᴰ A)
    unambiguous⊕ᴰ-from-disjoint = π≡→unambiguous the-π≡
      where
      distrib≅ : (⊕ᴰ A) & (⊕ᴰ A) ≅ ⊕[ x ∈ X ] (⊕[ y ∈ X ] (A x & A y))
      distrib≅ = &⊕ᴰ-distL≅ ≅∙ ⊕ᴰ≅ (λ _ → &⊕ᴰ-distR≅)

      inner : π₁ {A = ⊕ᴰ A} {B = ⊕ᴰ A} ∘g distrib≅ .inv
            ≡ π₂ {A = ⊕ᴰ A} {B = ⊕ᴰ A} ∘g distrib≅ .inv
      inner = ⊕ᴰ≡ _ _ (λ x → ⊕ᴰ≡ _ _ (λ y → cases x y))

      the-π≡ : π₁ {A = ⊕ᴰ A} {B = ⊕ᴰ A} ≡ π₂
      the-π≡ =
        cong (π₁ ∘g_) (sym (distrib≅ .ret))
        ∙ cong (_∘g distrib≅ .fun) inner
        ∙ cong (π₂ ∘g_) (distrib≅ .ret)

