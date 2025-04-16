open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Sum.Binary.AsPrimitive.Properties (Alphabet : hSet ℓ-zero) where

import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool using (Bool ; false ; true ; _≟_ ; isSetBool ; true≢false)
open import Cubical.Data.FinSet
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.Function Alphabet
open import Grammar.Product Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Distributivity Alphabet
import Grammar.Sum.Binary.AsIndexed.Base Alphabet as Ind⊕
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD  : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

module _ (A : Bool → Grammar ℓA) where
  Ind⊕→⊕ : ⊕ᴰ A ⊢ A true ⊕ A false
  Ind⊕→⊕ = Ind⊕.⊕-elim inl inr

  ⊕→Ind⊕ : A true ⊕ A false ⊢ ⊕ᴰ A
  ⊕→Ind⊕ = ⊕-elim Ind⊕.inl Ind⊕.inr

  private
    opaque
      unfolding _⊕_ ⊕-elim
      @0 the-sec : ⊕→Ind⊕ ∘g Ind⊕→⊕ ≡ id
      the-sec = ⊕ᴰ≡ _ _ λ where
        true → refl
        false → refl

      @0 the-ret : Ind⊕→⊕ ∘g ⊕→Ind⊕ ≡ id
      the-ret = ⊕≡ _ _ refl refl

  ⊕≅⊕Ind : A true ⊕ A false ≅ ⊕ᴰ A
  ⊕≅⊕Ind .fun = ⊕→Ind⊕
  ⊕≅⊕Ind .inv = Ind⊕→⊕
  ⊕≅⊕Ind .sec = the-sec
  ⊕≅⊕Ind .ret = the-ret

module _ {A B : Grammar ℓA} (unambig⊕ : unambiguous (A ⊕ B)) where
  @0 unambig-⊕-is-disjoint : disjoint A B
  unambig-⊕-is-disjoint =
    disjoint≅2
      (hasDisjointSummands⊕ᴰ isSetBool
        (unambiguous≅ (⊕≅⊕Ind (Ind⊕.⊕Ind A B)) unambig⊕)
        true false true≢false)
      id≅ id≅

  @0 summand-L-is-unambig : unambiguous A
  summand-L-is-unambig =
    unambiguous≅ id≅
      (unambiguous⊕ᴰ isSetBool (unambiguous≅ (⊕≅⊕Ind (Ind⊕.⊕Ind A B)) unambig⊕) true)

  @0 summand-R-is-unambig : unambiguous B
  summand-R-is-unambig =
    unambiguous≅ id≅
      (unambiguous⊕ᴰ isSetBool (unambiguous≅ (⊕≅⊕Ind (Ind⊕.⊕Ind A B)) unambig⊕) false)

open StrongEquivalence
open WeakEquivalence
module _
  {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC} {D : Grammar ℓD}
  (A≈B : A ≈ B)
  (dis-AC : disjoint A C)
  (dis-BD : disjoint B D)
  (A⊕C≅B⊕D : (A ⊕ C) ≈ (B ⊕ D))
  where
  disjoint⊕≈ : C ≈ D
  disjoint⊕≈ .fun =
    ⊕-elim
      (⊥-elim ∘g dis-AC ∘g A≈B .inv ,&p id)
      π₁
    ∘g &⊕-distR
    ∘g (A⊕C≅B⊕D .fun ∘g inr) ,&p id
    ∘g &-Δ
  disjoint⊕≈ .inv =
    ⊕-elim
      (⊥-elim ∘g dis-BD ∘g A≈B .fun ,&p id)
      π₁
    ∘g &⊕-distR
    ∘g (A⊕C≅B⊕D .inv ∘g inr) ,&p id
    ∘g &-Δ

open isStrongEquivalence
@0 isMono-⊕-inl : isMono (inl {A = A} {B = B})
isMono-⊕-inl {A = A}{B = B}{C = C} e e' inl∘e≡inl∘e' =
  sym (&-β₂ _ _) ∙ cong (π₂ ∘g_) r ∙ &-β₂ _ _
  where
  @0 isMono-C&A→C&A⊕C&B : isMono (inl {A = C & A } {B = C & B})
  isMono-C&A→C&A⊕C&B =
    hasRetraction→isMono inl (⊕-elim id (id ,& e ∘g π₁))
      (⊕-βl id (id ,& e ∘g π₁))

  distiso∘inl = (&⊕-distL⁻ ∘g inl {A = C & A}{B = C & B})
  @0 isMono-distiso∘inl :
    isMono (&⊕-distL⁻ ∘g inl {A = C & A}{B = C & B})
  isMono-distiso∘inl =
    Mono∘g (inl {A = C & A}{B = C & B}) &⊕-distL⁻
      (isStrongEquivalence→isMono &⊕-distL⁻
        (isStrEq &⊕-distL (&⊕-distL≅ .ret) (&⊕-distL≅ .sec)))
      isMono-C&A→C&A⊕C&B

  p : id ,& (inl {A = A}{B = B} ∘g e) ≡ id ,& (inl {A = A}{B = B} ∘g e')
  p = &-η' _ _
    (&-β₁ id _ ∙ sym (&-β₁ id _))
    (&-β₂ _ _ ∙ inl∘e≡inl∘e' ∙ sym (&-β₂ _ _))

  opaque
    unfolding &-intro ⊕-elim π₁
    q : distiso∘inl ∘g (id ,& e) ≡ distiso∘inl ∘g (id ,& e')
    q = p

  @0 r : (id {A = C} ,& e) ≡ (id ,& e')
  r = isMono-distiso∘inl (id ,& e) (id ,& e') q

@0 isMono-⊕-inr : isMono (inr {A = B} {B = A})
isMono-⊕-inr {B = B}{A = A}{C = C} e e' inr∘e≡inr∘e' =
  sym (&-β₂ _ _) ∙ cong (π₂ ∘g_) r ∙ &-β₂ _ _
  where
  isMono-C&B→C&A⊕C&B : isMono (inr {A = C & B} {B = C & A})
  isMono-C&B→C&A⊕C&B =
    hasRetraction→isMono inr
      (⊕-elim (π₁ ,& (e ∘g π₁)) id)
      (⊕-βr (π₁ ,& (e ∘g π₁)) id)

  distiso∘inr = (&⊕-distL⁻ ∘g inr {A = C & B}{B = C & A})
  isMono-distiso∘inr :
    isMono (&⊕-distL⁻ ∘g inr {A = C & B}{B = C & A})
  isMono-distiso∘inr =
    Mono∘g (inr {A = C & B}{B = C & A}) &⊕-distL⁻
      (isStrongEquivalence→isMono &⊕-distL⁻
        (isStrEq &⊕-distL (&⊕-distL≅ .ret) (&⊕-distL≅ .sec)))
      isMono-C&B→C&A⊕C&B

  p : id ,& (inr {A = B}{B = A} ∘g e) ≡ id ,& (inr {A = B}{B = A} ∘g e')
  p = &-η' _ _
    (&-β₁ id _ ∙ sym (&-β₁ id _))
    (&-β₂ _ _ ∙ inr∘e≡inr∘e' ∙ sym (&-β₂ _ _))

  opaque
    unfolding &-intro ⊕-elim π₁
    q : distiso∘inr ∘g id ,& e ≡ distiso∘inr ∘g id ,& e'
    q = p

  r : (id {A = C} ,& e) ≡ (id ,& e')
  r = isMono-distiso∘inr (id ,& e) (id ,& e') q
