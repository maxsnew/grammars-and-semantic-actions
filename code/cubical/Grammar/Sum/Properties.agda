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
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

module _ {g : Grammar ℓg} {h : Grammar ℓh}
  (disjoint-summands : disjoint g h)
  (unambig-g : unambiguous g)
  (unambig-h : unambiguous h)
  where

  open InductiveSum g h

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
            (comp-strong-equiv (LiftG≅ ℓh g) (LiftG≅ (ℓ-max ℓg ℓh) (LiftG ℓh g)))
            unambig-g
      ; ⊕IndTag.R →
          unambiguous≅
            (comp-strong-equiv (LiftG≅ ℓg h) (LiftG≅ (ℓ-max ℓg ℓh) (LiftG ℓg h)))
            unambig-h
       })
      (isFinSet→Discrete isFinSet⊕IndTag)

  unambiguous⊕ : unambiguous (g ⊕ h)
  unambiguous⊕ =
    unambiguous≅
    (comp-strong-equiv
      (sym-strong-equivalence unroll⊕Ind≅)
      (sym-strong-equivalence ⊕≅⊕Ind)
    )
    unambiguous-⊕Ind'

module _ (unambig⊕ : unambiguous (g ⊕ h)) where
  open InductiveSum g h
  unambig-⊕-is-disjoint : disjoint g h
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

  summand-L-is-unambig : unambiguous g
  summand-L-is-unambig =
    unambiguous≅
      (sym≅ (LiftG≅2 _ _ _))
      (unambiguous⊕ᴰ
        (isFinSet→isSet isFinSet⊕IndTag)
        (unambiguous≅ (⊕≅⊕Ind ≅∙ unroll⊕Ind≅) unambig⊕)
        L)

  summand-R-is-unambig : unambiguous h
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
  {g : Grammar ℓg} {h : Grammar ℓh} {k : Grammar ℓk} {l : Grammar ℓl}
  (g≈h : g ≈ h)
  (dis-gk : disjoint g k)
  (dis-hl : disjoint h l)
  (g⊕k≅h⊕l : (g ⊕ k) ≈ (h ⊕ l))
  where
  disjoint⊕≈ : k ≈ l
  disjoint⊕≈ .fun =
    ⊕-elim
      (⊥-elim ∘g dis-gk ∘g g≈h .inv ,&p id)
      &-π₁
    ∘g &⊕-distR
    ∘g (g⊕k≅h⊕l .fun ∘g ⊕-inr) ,&p id
    ∘g &-Δ
  disjoint⊕≈ .inv =
    ⊕-elim
      (⊥-elim ∘g dis-hl ∘g g≈h .fun ,&p id)
      &-π₁
    ∘g &⊕-distR
    ∘g (g⊕k≅h⊕l .inv ∘g ⊕-inr) ,&p id
    ∘g &-Δ
