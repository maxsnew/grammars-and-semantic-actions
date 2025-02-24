open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.KleeneStar.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.FinSet
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Product Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Dependent.Unambiguous Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.Properties Alphabet
open import Term.Base Alphabet

private
  variable
    ℓG ℓH : Level
    g h : Grammar ℓG

open StrongEquivalence
module _ (g : Grammar ℓG) where
  opaque
    unfolding ⊕-elim ⊗-intro
    unrolled*≅ε⊕g⊗g* : unrolled* g ≅ (ε ⊕ g ⊗ g *)
    unrolled*≅ε⊕g⊗g* =
      mkStrEq
        (⊕ᴰ-elim (λ {
          nil → ⊕-inl ∘g lowerG ∘g lowerG
        ; cons → ⊕-inr ∘g (lowerG ,⊗ lowerG)
        }))
        (⊕-elim
          (⊕ᴰ-in nil ∘g liftG ∘g liftG)
          (⊕ᴰ-in cons ∘g (liftG ,⊗ liftG))
        )
        (⊕≡ _ _ refl refl)
        (⊕ᴰ≡ _ _ λ {
          nil → refl
        ; cons → refl
        })

    unrolled*L≅ε⊕g*L⊗g : unrolled*L g ≅ (ε ⊕ (*L g ⊗ g))
    unrolled*L≅ε⊕g*L⊗g =
      mkStrEq
        (⊕ᴰ-elim (λ {
          nil → ⊕-inl ∘g lowerG ∘g lowerG
        ; snoc → ⊕-inr ∘g (lowerG ,⊗ lowerG)
        }))
        (⊕-elim
          (⊕ᴰ-in nil ∘g liftG ∘g liftG)
          (⊕ᴰ-in snoc ∘g (liftG ,⊗ liftG))
        )
        (⊕≡ _ _ refl refl)
        (⊕ᴰ≡ _ _ λ {
          nil → refl
        ; snoc → refl
        })

  *≅ε⊕g⊗g* : (g *) ≅ (ε ⊕ g ⊗ (g *))
  *≅ε⊕g⊗g* = comp-strong-equiv (*≅unrolled* g) unrolled*≅ε⊕g⊗g*

  *≅ε⊕g*⊗g : (g *) ≅ (ε ⊕ (g * ⊗ g))
  *≅ε⊕g*⊗g =
    *≅*L g
    ≅∙ *L≅unrolled*L g
    ≅∙ unrolled*L≅ε⊕g*L⊗g
    ≅∙ ⊕≅ id≅ (⊗≅ (sym≅ (*≅*L g)) id≅)
