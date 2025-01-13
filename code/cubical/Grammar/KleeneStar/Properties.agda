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

  *≅ε⊕g⊗g* : (g *) ≅ (ε ⊕ g ⊗ (g *))
  *≅ε⊕g⊗g* = comp-strong-equiv (*≅unrolled* g) unrolled*≅ε⊕g⊗g*

  -- module _
  --   (not-nullable : g & ε ⊢ ⊥) where
  --   not-nullable-g+ : (g +) & ε ⊢ ⊥
  --   not-nullable-g+ =
  --     {!!}
  --     ∘g {!!}
  --     ∘g {!? ,&p ?!}


  -- module _
  --   (unambig-g : unambiguous g)
  --   (not-nullable : g & ε ⊢ ⊥)
  --   (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  --   opaque
  --     unfolding ⊗-intro
  --     unambig-unrolled* : unambiguous (unrolled* g)
  --     unambig-unrolled* =
  --       mkUnambiguous⊕ᴰ
  --       (λ {
  --         nil nil → λ x → Empty.rec (x refl)
  --       ; nil cons → λ nil≢cons →
  --         (not-nullable-g+ not-nullable ∘g &-swap)
  --         ∘g ((lowerG ∘g lowerG) ,&p lowerG ,⊗ lowerG)
  --       ; cons nil → λ cons≢nil →
  --         not-nullable-g+ not-nullable
  --         ∘g (lowerG ,⊗ lowerG) ,&p (lowerG ∘g lowerG)
  --       ; cons cons → λ x → Empty.rec (x refl)
  --       })
  --       (λ {
  --         nil → unambiguous≅ (LiftG≅ ℓG ε*) (unambiguousε* isFinSetAlphabet)
  --       ; cons → unambiguous≅
  --         (mkStrEq
  --           ((liftG ,⊗ liftG))
  --           (lowerG ,⊗ lowerG) refl refl)
  --         {!!}
  --       })
  --       isFinSetAlphabet
  --       (isFinSet→Discrete (isFinSet*Tag g))
