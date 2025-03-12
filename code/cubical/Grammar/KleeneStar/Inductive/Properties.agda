open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.KleeneStar.Inductive.Properties (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Binary.Cartesian Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar.Inductive.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

open StrongEquivalence
module _ (A : Grammar ℓA) where
  opaque
    unfolding ⊕-elim ⊗-intro
    unrolled*≅ε⊕A⊗A* : unrolled* A ≅ (ε ⊕ A ⊗ A *)
    unrolled*≅ε⊕A⊗A* =
      mkStrEq
        (⊕ᴰ-elim (λ {
          nil → inl ∘g lowerG ∘g lowerG
        ; cons → inr ∘g (lowerG ,⊗ lowerG)
        }))
        (⊕-elim
          (σ nil ∘g liftG ∘g liftG)
          (σ cons ∘g (liftG ,⊗ liftG))
        )
        (⊕≡ _ _ refl refl)
        (⊕ᴰ≡ _ _ λ {
          nil → refl
        ; cons → refl
        })

    unrolled*L≅ε⊕A*L⊗A : unrolled*L A ≅ (ε ⊕ (*L A ⊗ A))
    unrolled*L≅ε⊕A*L⊗A =
      mkStrEq
        (⊕ᴰ-elim (λ {
          nil → inl ∘g lowerG ∘g lowerG
        ; snoc → inr ∘g (lowerG ,⊗ lowerG)
        }))
        (⊕-elim
          (σ nil ∘g liftG ∘g liftG)
          (σ snoc ∘g (liftG ,⊗ liftG))
        )
        (⊕≡ _ _ refl refl)
        (⊕ᴰ≡ _ _ λ {
          nil → refl
        ; snoc → refl
        })

  *≅ε⊕A⊗A* : (A *) ≅ (ε ⊕ A ⊗ (A *))
  *≅ε⊕A⊗A* = comp-strong-equiv (*≅unrolled* A) unrolled*≅ε⊕A⊗A*

  *≅ε⊕A*⊗A : (A *) ≅ (ε ⊕ (A * ⊗ A))
  *≅ε⊕A*⊗A =
    *≅*L A
    ≅∙ *L≅unrolled*L A
    ≅∙ unrolled*L≅ε⊕A*L⊗A
    ≅∙ ⊕≅ id≅ (⊗≅ (sym≅ (*≅*L A)) id≅)
