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
open import Grammar.HLevels.Properties Alphabet
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
