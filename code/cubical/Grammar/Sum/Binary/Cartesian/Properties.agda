open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Sum.Binary.Cartesian.Properties (Alphabet : hSet ℓ-zero) where

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
open import Grammar.Sum.Binary.Cartesian.Base Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Distributivity Alphabet
import Grammar.Sum.Binary.Inductive.Base Alphabet as Ind⊕
open import Grammar.Product.Binary.Cartesian.Base Alphabet
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
      the-sec : ⊕→Ind⊕ ∘g Ind⊕→⊕ ≡ id
      the-sec = ⊕ᴰ≡ _ _ λ where
        true → refl
        false → refl

      the-ret : Ind⊕→⊕ ∘g ⊕→Ind⊕ ≡ id
      the-ret = ⊕≡ _ _ refl refl
  ⊕≅⊕Ind : A true ⊕ A false ≅ ⊕ᴰ A
  ⊕≅⊕Ind .fun = ⊕→Ind⊕
  ⊕≅⊕Ind .inv = Ind⊕→⊕
  ⊕≅⊕Ind .sec = the-sec
  ⊕≅⊕Ind .ret = the-ret

module _ {A B : Grammar ℓA}
  (disjoint-summands : disjoint A B)
  (unambig-A : unambiguous A)
  (unambig-B : unambiguous B)
  where

  unambiguousInd⊕ : unambiguous (A Ind⊕.⊕ B)
  unambiguousInd⊕ =
    mkUnambiguous⊕ᴰ
      (λ where
        true true neq → Empty.rec (neq refl)
        false true neq → disjoint-summands ∘g &-swap
        true false neq → disjoint-summands
        false false neq → Empty.rec (neq refl)
      )
      (λ where
        true → unambig-A
        false → unambig-B)
      _≟_

  unambiguous⊕ : unambiguous (A ⊕ B)
  unambiguous⊕ = unambiguous≅ (sym≅ (⊕≅⊕Ind (Ind⊕.⊕Ind A B))) unambiguousInd⊕

module _ {A B : Grammar ℓA} (unambig⊕ : unambiguous (A ⊕ B)) where
  unambig-⊕-is-disjoint : disjoint A B
  unambig-⊕-is-disjoint =
    disjoint≅2
      (hasDisjointSummands⊕ᴰ isSetBool
        (unambiguous≅ (⊕≅⊕Ind (Ind⊕.⊕Ind A B)) unambig⊕)
        true false true≢false)
      id≅ id≅

  summand-L-is-unambig : unambiguous A
  summand-L-is-unambig =
    unambiguous≅ id≅
      (unambiguous⊕ᴰ isSetBool (unambiguous≅ (⊕≅⊕Ind (Ind⊕.⊕Ind A B)) unambig⊕) true)

  summand-R-is-unambig : unambiguous B
  summand-R-is-unambig =
    unambiguous≅ id≅
      (unambiguous⊕ᴰ isSetBool (unambiguous≅ (⊕≅⊕Ind (Ind⊕.⊕Ind A B)) unambig⊕) false)

open StrongEquivalence
open LogicalEquivalence
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
