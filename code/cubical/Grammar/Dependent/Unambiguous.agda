open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent.Unambiguous (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Product Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Dependent.Properties Alphabet
open import Grammar.Top Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet

private
  variable
    ℓA ℓB ℓX : Level

module _
  {X : Type ℓX} {A : X → Grammar ℓA}
  (isSetX : isSet X)
  where

  isMono-⊕ᴰ-in : (x : X) → isMono (⊕ᴰ-in {A = A} x)
  isMono-⊕ᴰ-in x e e' !∘e=!∘e' =
    funExt λ w → funExt λ p →
      sym (transportRefl (e w p)) ∙
      Σ-contractFst (refl , (isSetX _ _ _)) .fst
        (PathΣ→ΣPathTransport _ _ (funExt⁻ (funExt⁻ !∘e=!∘e' w) p))

  unambiguous'⊕ᴰ :
    unambiguous' (⊕[ x ∈ X ] A x) →
      (x : X)  → unambiguous' (A x)
  unambiguous'⊕ᴰ unambig⊕ x f f' !≡ =
    isMono-⊕ᴰ-in x f f'
      (unambig⊕ (⊕ᴰ-in x ∘g f) (⊕ᴰ-in x ∘g f')
        -- Need to change the endpoints of !≡ to line up with the
        -- ⊤-intro at the proper domain
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
      hasDisjointSummands⊕ᴰ : disjointSummands⊕ᴰ A
      hasDisjointSummands⊕ᴰ x y x≠y w (p , p') =
        x≠y λ i → unambig⊕ (⊕ᴰ-in x ∘g &-π₁) (⊕ᴰ-in y ∘g &-π₂) i w (p , p') .fst

    equalizer→⊥ :
      (x y : X) →
      (x ≡ y → Empty.⊥) →
      equalizer (⊕ᴰ-in x ∘g &-π₁) (⊕ᴰ-in y ∘g &-π₂) ⊢ ⊥
    equalizer→⊥ x y x≠y =
     hasDisjointSummands⊕ᴰ x y x≠y
     ∘g eq-π (⊕ᴰ-in x ∘g &-π₁) (⊕ᴰ-in y ∘g &-π₂)

module _ {X : Type ℓX} {A : X → Grammar ℓA}
  (disjoint-summands : disjointSummands⊕ᴰ A)
  (isLang-summands : ∀ x → isLang (A x))
  (discX : Discrete X)
  where

  opaque
    unfolding ⊥ _&_
    mkIsLang⊕ᴰ : isLang (⊕[ x ∈ X ] A x)
    mkIsLang⊕ᴰ w x y =
      decRec
        (λ x₁≡y₁ → Σ≡Prop (λ a → isLang-summands a w) x₁≡y₁)
        (λ ¬x₁≡y₁ →
          Empty.rec (disjoint-summands (x .fst) (y .fst) ¬x₁≡y₁ w (x .snd , y .snd))
        )
        (discX (x .fst) (y .fst))

module _ {X : Type ℓX} {A : X → Grammar ℓA}
  (disjoint-summands : disjointSummands⊕ᴰ A)
  (unambig-summands : ∀ x → unambiguous (A x))
  (discX : Discrete X)
  where

  mkUnambiguous⊕ᴰ : unambiguous (⊕[ x ∈ X ] A x)
  mkUnambiguous⊕ᴰ =
    EXTERNAL.isLang→unambiguous
      (mkIsLang⊕ᴰ disjoint-summands
        (λ a → EXTERNAL.unambiguous→isLang
          (unambig-summands a)) discX)
