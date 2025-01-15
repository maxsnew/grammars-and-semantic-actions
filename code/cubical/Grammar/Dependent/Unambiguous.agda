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
    ℓg ℓh ℓS : Level

module _
  {A : Type ℓS} {h : A → Grammar ℓh}
  (isSetA : isSet A)
  where

  isMono-⊕ᴰ-in : (a : A) → isMono (⊕ᴰ-in {h = h} a)
  isMono-⊕ᴰ-in a e e' !∘e=!∘e' =
    funExt λ w → funExt λ p →
      sym (transportRefl (e w p)) ∙
      Σ-contractFst (refl , (isSetA _ _ _)) .fst
        (PathΣ→ΣPathTransport _ _ (funExt⁻ (funExt⁻ !∘e=!∘e' w) p))

  unambiguous'⊕ᴰ :
    unambiguous' (⊕[ a ∈ A ] h a) →
      (a : A)  → unambiguous' (h a)
  unambiguous'⊕ᴰ unambig⊕ a f f' !≡ =
    isMono-⊕ᴰ-in a f f'
      (unambig⊕ (LinΣ-intro a ∘g f) (LinΣ-intro a ∘g f')
        -- Need to change the endpoints of !≡ to line up with the
        -- ⊤-intro at the proper domain
        (unambiguous⊤ _ _ ∙ !≡ ∙ sym (unambiguous⊤ _ _)))

  unambiguous⊕ᴰ : unambiguous (⊕[ a ∈ A ] h a) → (a : A) →
    unambiguous (h a)
  unambiguous⊕ᴰ unambig⊕ a =
    unambiguous'→unambiguous
      (unambiguous'⊕ᴰ (unambiguous→unambiguous' unambig⊕) a)

  module _
    (unambig⊕ : unambiguous (⊕[ a ∈ A ] h a))
    where
    opaque
      unfolding _&_ ⊥
      hasDisjointSummands⊕ᴰ : disjointSummands⊕ᴰ h
      hasDisjointSummands⊕ᴰ a a' a≠a' w (p , p') =
        a≠a' λ i → unambig⊕ (⊕ᴰ-in a ∘g &-π₁) (⊕ᴰ-in a' ∘g &-π₂) i w (p , p') .fst

    equalizer→⊥ :
      (a a' : A) →
      (a ≡ a' → Empty.⊥) →
      equalizer (⊕ᴰ-in a ∘g &-π₁) (⊕ᴰ-in a' ∘g &-π₂) ⊢ ⊥
    equalizer→⊥ a a' a≠a' =
     hasDisjointSummands⊕ᴰ a a' a≠a'
     ∘g eq-π (⊕ᴰ-in a ∘g &-π₁) (⊕ᴰ-in a' ∘g &-π₂)

module _ {A : Type ℓS} {h : A → Grammar ℓh}
  (disjoint-summands : disjointSummands⊕ᴰ h)
  (isLang-summands : ∀ a → isLang (h a))
  (discA : Discrete A)
  where

  opaque
    unfolding ⊥ _&_
    mkIsLang⊕ᴰ : isLang (⊕[ a ∈ A ] h a)
    mkIsLang⊕ᴰ w x y =
      decRec
        (λ x₁≡y₁ → Σ≡Prop (λ a → isLang-summands a w) x₁≡y₁)
        (λ ¬x₁≡y₁ →
          Empty.rec (disjoint-summands (x .fst) (y .fst) ¬x₁≡y₁ w (x .snd , y .snd))
        )
        (discA (x .fst) (y .fst))

module _ {A : Type ℓS} {h : A → Grammar ℓh}
  (disjoint-summands : disjointSummands⊕ᴰ h)
  (unambig-summands : ∀ a → unambiguous (h a))
  (discA : Discrete A)
  where

  mkUnambiguous⊕ᴰ : unambiguous (⊕[ a ∈ A ] h a)
  mkUnambiguous⊕ᴰ =
    EXTERNAL.isLang→unambiguous
      (mkIsLang⊕ᴰ disjoint-summands
        (λ a → EXTERNAL.unambiguous→isLang
          (unambig-summands a)) discA)
