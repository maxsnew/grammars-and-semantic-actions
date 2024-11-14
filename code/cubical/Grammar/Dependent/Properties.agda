open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Product Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Top Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet

private
  variable
    ℓg ℓh ℓS : Level

module _ {A : Type ℓS} {g : Grammar ℓg}{h : A → Grammar ℓh} where
  open StrongEquivalence
  opaque
    unfolding _⊗_
    ⊕ᴰ-distL :
      StrongEquivalence
        ((⊕[ a ∈ A ] h a) ⊗ g)
        (⊕[ a ∈ A ] (h a ⊗ g))
    ⊕ᴰ-distL .fun w (s , (a , x) , y) = a , ((s , (x , y)))
    ⊕ᴰ-distL .inv w (a , (s , (x , y))) = s , ((a , x) , y)
    ⊕ᴰ-distL .sec = refl
    ⊕ᴰ-distL .ret = refl

    ⊕ᴰ-distR :
      StrongEquivalence
        (g ⊗ (⊕[ a ∈ A ] h a))
        (⊕[ a ∈ A ] (g ⊗ h a))
    ⊕ᴰ-distR .fun w (s , x , (a , y)) = a , ((s , (x , y)))
    ⊕ᴰ-distR .inv w (a , (s , (x , y))) = s , (x , (a , y))
    ⊕ᴰ-distR .sec = refl
    ⊕ᴰ-distR .ret = refl

    &ᴰ-strengthL :
        (&[ a ∈ A ] h a) ⊗ g ⊢ &[ a ∈ A ] (h a ⊗ g)
    &ᴰ-strengthL w (s , f , pg) a = s , (f a , pg)

    &ᴰ-strengthR :
        g ⊗ (&[ a ∈ A ] h a) ⊢ &[ a ∈ A ] (g ⊗ h a)
    &ᴰ-strengthR w (s , pg , f) a = s , (pg , f a)

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
    (a a' : A)
    where
    opaque
      unfolding _&_ ⊥
      disjointSummands :
        (a ≡ a' → Empty.⊥) →
        disjoint (h a) (h a')
      disjointSummands a≠a' w (p , p') =
        a≠a' λ i → unambig⊕ (⊕ᴰ-in a ∘g &-π₁) (⊕ᴰ-in a' ∘g &-π₂) i w (p , p') .fst

    equalizer→⊥ :
      (a ≡ a' → Empty.⊥) →
      equalizer (⊕ᴰ-in a ∘g &-π₁) (⊕ᴰ-in a' ∘g &-π₂) ⊢ ⊥
    equalizer→⊥ a≠a' =
     disjointSummands a≠a'
     ∘g eq-π (⊕ᴰ-in a ∘g &-π₁) (⊕ᴰ-in a' ∘g &-π₂)

module _
  {X : Type ℓS} {A : X → Grammar ℓh}
  where
  isSetGrammar&ᴰ : (∀ x → isSetGrammar (A x)) → isSetGrammar (&ᴰ A)
  isSetGrammar&ᴰ isSetGrammarA w = isSetΠ λ x → isSetGrammarA x w

  isSetGrammar⊕ᴰ : isSet X → (∀ x → isSetGrammar (A x)) → isSetGrammar (⊕ᴰ A)
  isSetGrammar⊕ᴰ isSetX isSetGrammarA w = isSetΣ isSetX (λ x → isSetGrammarA x w)
