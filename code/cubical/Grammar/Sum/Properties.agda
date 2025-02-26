open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Sum.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinSet
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.Function Alphabet
open import Grammar.Product Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Dependent.Unambiguous Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD  : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

module _ {A : Grammar ℓA} {B : Grammar ℓB}
  (disjoint-summands : disjoint A B)
  (unambig-A : unambiguous A)
  (unambig-B : unambiguous B)
  where

  open InductiveSum A B

  unambiguous-⊕Ind' : unambiguous ⊕Ind'
  unambiguous-⊕Ind' =
    mkUnambiguous⊕ᴰ
      (λ {
        L R → λ L≢R →
          disjoint-summands
          ∘g (lowerG ∘g lowerG) ,&p (lowerG ∘g lowerG)
      ; L L → λ p → Empty.rec (p refl)
      ; R L → λ R≢L →
          disjoint-summands
          ∘g &-swap
          ∘g (lowerG ∘g lowerG) ,&p (lowerG ∘g lowerG)
      ; R R → λ p → Empty.rec (p refl)
      })
      (λ {
        ⊕IndTag.L →
          unambiguous≅
            (comp-strong-equiv (LiftG≅ ℓB A) (LiftG≅ (ℓ-max ℓA ℓB) (LiftG ℓB A)))
            unambig-A
      ; ⊕IndTag.R →
          unambiguous≅
            (comp-strong-equiv (LiftG≅ ℓA B) (LiftG≅ (ℓ-max ℓA ℓB) (LiftG ℓA B)))
            unambig-B
       })
      (isFinSet→Discrete isFinSet⊕IndTag)

  unambiguous⊕ : unambiguous (A ⊕ B)
  unambiguous⊕ =
    unambiguous≅
    (comp-strong-equiv
      (sym-strong-equivalence unroll⊕Ind≅)
      (sym-strong-equivalence ⊕≅⊕Ind)
    )
    unambiguous-⊕Ind'

module _ (unambig⊕ : unambiguous (A ⊕ B)) where
  open InductiveSum A B
  unambig-⊕-is-disjoint : disjoint A B
  unambig-⊕-is-disjoint =
    disjoint≅2
      (hasDisjointSummands⊕ᴰ
        (isFinSet→isSet isFinSet⊕IndTag)
        (unambiguous≅ (⊕≅⊕Ind ≅∙ unroll⊕Ind≅) unambig⊕)
        L
        R
        L≢R)
      (sym≅ (LiftG≅2 _ _ _))
      (sym≅ (LiftG≅2 _ _ _))

  summand-L-is-unambig : unambiguous A
  summand-L-is-unambig =
    unambiguous≅
      (sym≅ (LiftG≅2 _ _ _))
      (unambiguous⊕ᴰ
        (isFinSet→isSet isFinSet⊕IndTag)
        (unambiguous≅ (⊕≅⊕Ind ≅∙ unroll⊕Ind≅) unambig⊕)
        L)

  summand-R-is-unambig : unambiguous B
  summand-R-is-unambig =
    unambiguous≅
      (sym≅ (LiftG≅2 _ _ _))
      (unambiguous⊕ᴰ
        (isFinSet→isSet isFinSet⊕IndTag)
        (unambiguous≅ (⊕≅⊕Ind ≅∙ unroll⊕Ind≅) unambig⊕)
        R)

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
      &-π₁
    ∘g &⊕-distR
    ∘g (A⊕C≅B⊕D .fun ∘g ⊕-inr) ,&p id
    ∘g &-Δ
  disjoint⊕≈ .inv =
    ⊕-elim
      (⊥-elim ∘g dis-BD ∘g A≈B .fun ,&p id)
      &-π₁
    ∘g &⊕-distR
    ∘g (A⊕C≅B⊕D .inv ∘g ⊕-inr) ,&p id
    ∘g &-Δ
