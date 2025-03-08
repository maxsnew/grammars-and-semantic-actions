open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

module Grammar.Dependent.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Maybe hiding (rec)
import Cubical.Data.Empty as Empty

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Function Alphabet
open import Grammar.Product Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.Sum Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet

private
  variable
    ℓA ℓB ℓX ℓY : Level

open StrongEquivalence
module _ {X : Type ℓX} (A : X → Grammar ℓA) where
  disjointSummands⊕ᴰ : Type (ℓ-max ℓX ℓA)
  disjointSummands⊕ᴰ =
    ∀ x y → (x ≡ y → Empty.⊥) → disjoint (A x) (A y)

module _ {X : Type ℓX} {A : Grammar ℓA}{B : X → Grammar ℓB} where

  opaque
    unfolding _⊗_
    ⊕ᴰ-distL :
      StrongEquivalence
        ((⊕[ x ∈ X ] B x) ⊗ A)
        (⊕[ x ∈ X ] (B x ⊗ A))
    ⊕ᴰ-distL .fun w (s , (x , p) , q) = x , ((s , (p , q)))
    ⊕ᴰ-distL .inv w (x , (s , (p , q))) = s , ((x , p) , q)
    ⊕ᴰ-distL .sec = refl
    ⊕ᴰ-distL .ret = refl

    ⊕ᴰ-distR :
      StrongEquivalence
        (A ⊗ (⊕[ x ∈ X ] B x))
        (⊕[ x ∈ X ] (A ⊗ B x))
    ⊕ᴰ-distR .fun w (s , p , (x , q)) = x , ((s , (p , q)))
    ⊕ᴰ-distR .inv w (x , (s , (p , q))) = s , (p , (x , q))
    ⊕ᴰ-distR .sec = refl
    ⊕ᴰ-distR .ret = refl

    &ᴰ-strengthL :
        (&[ x ∈ X ] B x) ⊗ A ⊢ &[ x ∈ X ] (B x ⊗ A)
    &ᴰ-strengthL w (s , f , pA) x = s , (f x , pA)

    &ᴰ-strengthR :
        A ⊗ (&[ x ∈ X ] B x) ⊢ &[ x ∈ X ] (A ⊗ B x)
    &ᴰ-strengthR w (s , pA , f) x = s , (pA , f x)

module _
  {X : Type ℓX}
  {Y : X → Type ℓY}
  {A : Σ[ x ∈ X ] Y x → Grammar ℓA}
  where
  &ᴰ⊕ᴰ-dist :
    (&[ x ∈ X ] (⊕[ y ∈ Y x ] A (x , y))) ⊢
      ⊕[ f ∈ (∀ (x : X) → Y x) ] (&[ x ∈ X ] A (x , f x))
  &ᴰ⊕ᴰ-dist w z = (λ x → z x .fst) , λ x → z x .snd

  &ᴰ⊕ᴰ-dist⁻ :
    ⊕[ f ∈ (∀ (x : X) → Y x) ] (&[ x ∈ X ] A (x , f x)) ⊢
      (&[ x ∈ X ] (⊕[ y ∈ Y x ] A (x , y)))
  &ᴰ⊕ᴰ-dist⁻ = ⊕ᴰ-elim λ f → &ᴰ-in λ x → λ w z → (f x) , (z x)

  &ᴰ⊕ᴰ-dist≅  :
    (&[ x ∈ X ] (⊕[ y ∈ Y x ] A (x , y)))
      ≅
    (⊕[ f ∈ (∀ (x : X) → Y x) ] (&[ x ∈ X ] A (x , f x)))
  &ᴰ⊕ᴰ-dist≅ .fun = &ᴰ⊕ᴰ-dist
  &ᴰ⊕ᴰ-dist≅ .inv = &ᴰ⊕ᴰ-dist⁻
  &ᴰ⊕ᴰ-dist≅ .sec = refl
  &ᴰ⊕ᴰ-dist≅ .ret = refl

module _
  {X : Type ℓX}
  {A : X → Grammar ℓA}
  {B : X → Grammar ℓB}
  (A≅B : ∀ (x : X) → A x ≅ B x)
  where

  &ᴰ≅ : (&[ x ∈ X ] A x) ≅ &[ x ∈ X ] B x
  &ᴰ≅ .fun = map&ᴰ λ x → A≅B x .fun
  &ᴰ≅ .inv = map&ᴰ λ x → A≅B x .inv
  &ᴰ≅ .sec = &ᴰ≡ _ _ λ x → cong (_∘g &ᴰ-π x) (A≅B x .sec)
  &ᴰ≅ .ret = &ᴰ≡ _ _ λ x → cong (_∘g &ᴰ-π x) (A≅B x .ret)

  ⊕ᴰ≅ : (⊕[ x ∈ X ] A x) ≅ ⊕[ x ∈ X ] B x
  ⊕ᴰ≅ .fun = map⊕ᴰ λ x → A≅B x .fun
  ⊕ᴰ≅ .inv = map⊕ᴰ λ x → A≅B x .inv
  ⊕ᴰ≅ .sec = ⊕ᴰ≡ _ _ λ x → cong (⊕ᴰ-in x ∘g_) (A≅B x .sec)
  ⊕ᴰ≅ .ret = ⊕ᴰ≡ _ _ λ x → cong (⊕ᴰ-in x ∘g_) (A≅B x .ret)

module _
  {X : Type ℓX}
  {A : X → Grammar ℓA}
  {B : Grammar ℓB}
  where

  private
    the-fun : (⊕[ x ∈ X ] A x) & B ⊢ ⊕[ x ∈ X ] (A x & B)
    the-fun = ⇒-intro⁻ (⊕ᴰ-elim (λ x → ⇒-intro (⊕ᴰ-in x)))

    the-inv : ⊕[ x ∈ X ] (A x & B) ⊢ (⊕[ x ∈ X ] A x) & B
    the-inv = ⊕ᴰ-elim λ x → ⊕ᴰ-in x ,&p id

    opaque
      unfolding ⇒-intro &-intro
      the-sec : the-fun ∘g the-inv ≡ id
      the-sec = refl

      the-ret : the-inv ∘g the-fun ≡ id
      the-ret = refl

  &⊕ᴰ-distL≅ :
    (⊕[ x ∈ X ] A x) & B ≅ ⊕[ x ∈ X ] (A x & B)
  &⊕ᴰ-distL≅ = mkStrEq the-fun the-inv the-sec the-ret

  &⊕ᴰ-distR≅ :
    B & (⊕[ x ∈ X ] A x) ≅ ⊕[ x ∈ X ] (B & A x)
  &⊕ᴰ-distR≅ =
    &-swap≅
    ≅∙ &⊕ᴰ-distL≅
    ≅∙ ⊕ᴰ≅ λ a → &-swap≅

module _
  {X : Type ℓX}
  {Y : X → Type ℓY}
  {A : (x : X) → Y x → Grammar ℓA}
  where
  nested⊕ᴰ≅ :
    (⊕[ x ∈ X ] ⊕[ y ∈ Y x ] A x y) ≅ ⊕[ (x , y) ∈ Σ X Y ] A x y
  nested⊕ᴰ≅ .fun = ⊕ᴰ-elim (λ x → ⊕ᴰ-elim (λ y → ⊕ᴰ-in (x , y)))
  nested⊕ᴰ≅ .inv = ⊕ᴰ-elim (λ (x , y) → ⊕ᴰ-in x ∘g ⊕ᴰ-in y)
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
  ⊕⊕ᴰ≅ .fun = ⊕-elim (⊕ᴰ-in nothing ∘g liftG) (mapFst⊕ᴰ just (λ _ → liftG))
  ⊕⊕ᴰ≅ .inv = ⊕ᴰ-elim λ where
    nothing → ⊕-inl ∘g lowerG
    (just x) → ⊕-inr ∘g ⊕ᴰ-in x ∘g lowerG
  ⊕⊕ᴰ≅ .sec =
    ⊕ᴰ≡ _ _ λ where
      nothing i →
        ⊕-βl (⊕ᴰ-in nothing ∘g liftG) (mapFst⊕ᴰ just (λ _ → liftG)) i ∘g lowerG
      (just x) i →
        ⊕-βr
          (⊕ᴰ-in nothing ∘g liftG)
          (mapFst⊕ᴰ just (λ _ → liftG)) i
        ∘g ⊕ᴰ-in x ∘g lowerG
  ⊕⊕ᴰ≅ .ret =
    ⊕≡ _ _
      (λ i →
        inv ⊕⊕ᴰ≅
        ∘g ⊕-βl (⊕ᴰ-in nothing ∘g liftG) (mapFst⊕ᴰ just (λ _ → liftG)) i)
      (λ i →
        inv ⊕⊕ᴰ≅
        ∘g ⊕-βr (⊕ᴰ-in nothing ∘g liftG) (mapFst⊕ᴰ just (λ _ → liftG)) i)

module _
  {X : Type ℓX} {A : X → Grammar ℓA}
  where
  isSetGrammar&ᴰ : (∀ x → isSetGrammar (A x)) → isSetGrammar (&ᴰ A)
  isSetGrammar&ᴰ isSetGrammarA w = isSetΠ λ x → isSetGrammarA x w

  isSetGrammar⊕ᴰ : isSet X → (∀ x → isSetGrammar (A x)) → isSetGrammar (⊕ᴰ A)
  isSetGrammar⊕ᴰ isSetX isSetGrammarA w = isSetΣ isSetX (λ x → isSetGrammarA x w)
