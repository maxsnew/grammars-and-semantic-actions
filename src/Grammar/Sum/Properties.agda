{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Sigma
import Erased.Data.Empty.Base as Empty
import Erased.Data.Equality.Base as Eq
open import Erased.Data.Maybe.Base hiding (rec)

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Lift Alphabet isSetAlphabet
open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
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

open StrongEquivalence

module _ {X : Type ℓX} (A : X → Grammar ℓA) where
  disjointSummands⊕ᴰ : Type (ℓ-max ℓX ℓA)
  disjointSummands⊕ᴰ = ∀ x y → (x ≡ y → Empty.⊥) → disjoint (A x) (A y)

module _ {X : Type ℓX} {A : X → Grammar ℓA} {B : X → Grammar ℓB}
  (A≅B : ∀ (x : X) → A x ≅ B x)
  where
  ⊕ᴰ≅ : (⊕[ x ∈ X ] A x) ≅ ⊕[ x ∈ X ] B x
  ⊕ᴰ≅ .fun = map⊕ᴰ λ x → A≅B x .fun
  ⊕ᴰ≅ .inv = map⊕ᴰ λ x → A≅B x .inv
  ⊕ᴰ≅ .sec = ⊕ᴰ≡ _ _ λ x → cong (σ x ∘g_) (A≅B x .sec)
  ⊕ᴰ≅ .ret = ⊕ᴰ≡ _ _ λ x → cong (σ x ∘g_) (A≅B x .ret)

module _
  {X : Type ℓX}
  {Y : X → Type ℓY}
  {A : (x : X) → Y x → Grammar ℓA}
  where
  nested⊕ᴰ≅ : (⊕[ x ∈ X ] ⊕[ y ∈ Y x ] A x y) ≅ ⊕[ (x , y) ∈ Σ X Y ] A x y
  nested⊕ᴰ≅ .fun = ⊕ᴰ-elim (λ x → ⊕ᴰ-elim (λ y → σ (x , y)))
  nested⊕ᴰ≅ .inv = ⊕ᴰ-elim (λ (x , y) → σ x ∘g σ y)
  nested⊕ᴰ≅ .sec = refl
  nested⊕ᴰ≅ .ret = refl

module _
  {X : Type ℓX}
  (A : Grammar ℓA)
  (B : X → Grammar ℓB)
  where

  merge⊕ : Maybe X → Grammar (ℓ-max ℓA ℓB)
  merge⊕ nothing = LiftG ℓB A
  merge⊕ (just x) = LiftG ℓA (B x)

  ⊕⊕ᴰ≅ : A ⊕ (⊕[ x ∈ X ] B x) ≅ ⊕[ x? ∈ Maybe X ] merge⊕ x?
  ⊕⊕ᴰ≅ .fun = ⊕-elim (σ nothing ∘g liftG) (mapFst⊕ᴰ just (λ _ → liftG))
  ⊕⊕ᴰ≅ .inv = ⊕ᴰ-elim λ where
    nothing → inl ∘g lowerG
    (just x) → inr ∘g σ x ∘g lowerG
  ⊕⊕ᴰ≅ .sec =
    ⊕ᴰ≡ _ _ λ @0 where
      nothing i →
        ⊕-βl (σ nothing ∘g liftG) (mapFst⊕ᴰ just (λ _ → liftG)) i ∘g lowerG
      (just x) i →
        ⊕-βr
          (σ nothing ∘g liftG)
          (mapFst⊕ᴰ just (λ _ → liftG)) i
        ∘g σ x ∘g lowerG
  ⊕⊕ᴰ≅ .ret =
    ⊕≡ _ _
      (λ i →
        inv ⊕⊕ᴰ≅
        ∘g ⊕-βl (σ nothing ∘g liftG) (mapFst⊕ᴰ just (λ _ → liftG)) i)
      (λ i →
        inv ⊕⊕ᴰ≅
        ∘g ⊕-βr (σ nothing ∘g liftG) (mapFst⊕ᴰ just (λ _ → liftG)) i)

module _
  {X : Type ℓX} {A : X → Grammar ℓA}
  where

  @0 isSetGrammar⊕ᴰ : isSet X → (∀ x → isSetGrammar (A x)) → isSetGrammar (⊕ᴰ A)
  isSetGrammar⊕ᴰ isSetX isSetGrammarA w = isSetΣ isSetX (λ x → isSetGrammarA x w)
