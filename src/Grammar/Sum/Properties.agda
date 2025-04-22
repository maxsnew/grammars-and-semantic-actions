open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Data.Maybe hiding (rec)

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar.Base Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Properties Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
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

open StrongEquivalence

module _ {X : Type ℓX} (A : X → Grammar ℓA) where
  disjointSummands⊕ᴰ : Type (ℓ-max ℓX ℓA)
  disjointSummands⊕ᴰ =
    -- include an erased Eq proof as an argument to
    -- pattern match against
    ∀ x y → (@0 x ≡ y → @0 x Eq.≡ y → Empty.⊥) → disjoint (A x) (A y)

module _ {X : Type ℓX} {A : Grammar ℓA}{B : X → Grammar ℓB} where
  opaque
    unfolding _⊗_
    ⊕ᴰ-distL : (⊕[ x ∈ X ] B x) ⊗ A ≅ ⊕[ x ∈ X ] (B x ⊗ A)
    ⊕ᴰ-distL .fun w (s , (x , p) , q) = x , ((s , (p , q)))
    ⊕ᴰ-distL .inv w (x , (s , (p , q))) = s , ((x , p) , q)
    ⊕ᴰ-distL .sec = refl
    ⊕ᴰ-distL .ret = refl

    ⊕ᴰ-distR : A ⊗ (⊕[ x ∈ X ] B x) ≅ ⊕[ x ∈ X ] (A ⊗ B x)
    ⊕ᴰ-distR .fun w (s , p , (x , q)) = x , ((s , (p , q)))
    ⊕ᴰ-distR .inv w (x , (s , (p , q))) = s , (p , (x , q))
    ⊕ᴰ-distR .sec = refl
    ⊕ᴰ-distR .ret = refl

    opaque
      unfolding ⊗-intro
      @0 ⊕ᴰ-distL-β : ∀ {x : X} → ⊕ᴰ-distL .fun ∘g σ x ,⊗ id ≡ σ x
      ⊕ᴰ-distL-β = refl

      @0 ⊕ᴰ-distR-β : ∀ {x : X} → ⊕ᴰ-distR .fun ∘g id ,⊗ σ x ≡ σ x
      ⊕ᴰ-distR-β = refl

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
