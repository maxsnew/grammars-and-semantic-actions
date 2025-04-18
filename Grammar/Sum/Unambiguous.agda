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
