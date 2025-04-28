{-# OPTIONS --erased-cubical #-}
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
  where

  module _
    (@0 unambig⊕ : unambiguous (⊕[ x ∈ X ] A x))
    where
    opaque
      unfolding _&_ ⊥
      @0 equalizer→⊥ :
        (x y : X) →
        (x ≡ y → Empty.⊥) →
        equalizer (σ {A = A} x ∘g π₁) (σ y ∘g π₂) ⊢ ⊥
      equalizer→⊥ x y x≠y w p =
        x≠y (cong fst (funExt⁻ (funExt⁻ (eq-π-pf (σ {A = A} x ∘g π₁) (σ y ∘g π₂)) w) p))

    @0 hasDisjointSummands⊕ᴰ : disjointSummands⊕ᴰ A
    hasDisjointSummands⊕ᴰ x y x≠y =
      equalizer→⊥ x y x≠y
      ∘g eq-intro {A = A x & A y}{B = ⊕[ x ∈ X ] A x}
        (σ x ∘g π₁) (σ y ∘g π₂) id
        (unambig⊕ (σ x ∘g π₁) (σ y ∘g π₂))
