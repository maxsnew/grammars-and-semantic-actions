{-# OPTIONS --erased-cubical --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Unambiguous (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

import Erased.Data.Empty.Base as Empty
import Erased.Data.Equality.Base as Eq

open import Cubical.Data.Sigma
open import Cubical.Data.Maybe hiding (rec)

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Bottom Alphabet isSetAlphabet
open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Sum.Properties Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.Equalizer.AsPath.Base Alphabet isSetAlphabet
open import Grammar.HLevels.Base Alphabet isSetAlphabet
open import Grammar.Top Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

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
    @0 isMono-σ : (x : X) → isMono (σ {A = A} x)
    isMono-σ x e e' σe=σe' =
      funExt λ w → funExt λ p →
        sym (transportRefl (e w p)) ∙
        Σ-contractFst (refl , (isSetX _ _ _)) .fst
          (PathΣ→ΣPathTransport _ _ (funExt⁻ (funExt⁻ σe=σe' w) p))

  @0 unambiguous'⊕ᴰ :
    unambiguous' (⊕[ x ∈ X ] A x) →
      (x : X)  → unambiguous' (A x)
  unambiguous'⊕ᴰ unambig⊕ x f f' !≡ =
    isMono-σ x f f'
      (unambig⊕ (σ x ∘g f) (σ x ∘g f')
        (unambiguous⊤ _ _ ∙ !≡ ∙ sym (unambiguous⊤ _ _)))

  @0 unambiguous⊕ᴰ : unambiguous (⊕[ x ∈ X ] A x) → (x : X) →
    unambiguous (A x)
  unambiguous⊕ᴰ unambig⊕ x =
    unambiguous'→unambiguous
      (unambiguous'⊕ᴰ (unambiguous→unambiguous' unambig⊕) x)

  module _
    (@0 unambig⊕ : unambiguous (⊕[ x ∈ X ] A x))
    where
    opaque
      unfolding _&_ ⊥
      equalizer→⊥ :
        (x y : X) →
        (@0 x ≡ y → Empty.⊥) →
        equalizer (σ {A = A} x ∘g π₁) (σ y ∘g π₂) ⊢ ⊥
      equalizer→⊥ x y x≠y w p =
        x≠y (cong fst (funExt⁻ (funExt⁻ (eq-π-pf (σ {A = A} x ∘g π₁) (σ y ∘g π₂)) w) p))

    hasDisjointSummands⊕ᴰ : disjointSummands⊕ᴰ A
    hasDisjointSummands⊕ᴰ x y x≠y = {!!}
      -- equalizer→⊥ x y ?
      -- ∘g eq-intro {A = A x & A y}{B = ⊕[ x ∈ X ] A x}
      --   (σ x ∘g π₁) (σ y ∘g π₂) id
      --   (unambig⊕ (σ x ∘g π₁) (σ y ∘g π₂))
