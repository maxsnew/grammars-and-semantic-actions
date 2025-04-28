{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.KleeneStar.Inductive.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.Sum Alphabet isSetAlphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet isSetAlphabet
open import Grammar.Epsilon.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive.Base Alphabet isSetAlphabet
open import Grammar.Inductive.Indexed Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Lift Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

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
        (⊕ᴰ≡ _ _ λ @0 {
          nil → refl
        ; cons → refl
        })

    -- unrolled*L≅ε⊕A*L⊗A : unrolled*L A ≅ (ε ⊕ (*L A ⊗ A))
    -- unrolled*L≅ε⊕A*L⊗A =
    --   mkStrEq
    --     (⊕ᴰ-elim (λ {
    --       nil → inl ∘g lowerG ∘g lowerG
    --     ; snoc → inr ∘g (lowerG ,⊗ lowerG)
    --     }))
    --     (⊕-elim
    --       (σ nil ∘g liftG ∘g liftG)
    --       (σ snoc ∘g (liftG ,⊗ liftG))
    --     )
    --     (⊕≡ _ _ refl refl)
    --     (⊕ᴰ≡ _ _ λ {
    --       nil → refl
    --     ; snoc → refl
    --     })

  *≅ε⊕A⊗A* : (A *) ≅ (ε ⊕ A ⊗ (A *))
  *≅ε⊕A⊗A* = *≅unrolled* A ≅∙ unrolled*≅ε⊕A⊗A*

--   *≅ε⊕A*⊗A : (A *) ≅ (ε ⊕ (A * ⊗ A))
--   *≅ε⊕A*⊗A =
--     *≅*L A
--     ≅∙ *L≅unrolled*L A
--     ≅∙ unrolled*L≅ε⊕A*L⊗A
--     ≅∙ ⊕≅ id≅ (⊗≅ (sym≅ (*≅*L A)) id≅)

-- module _
--   {A B : Grammar ℓA}
--   (A≅B : A ≅ B)
--   where

--   private
--     the-A*-alg : Algebra (*Ty A) λ _ → B *
--     the-A*-alg _ = ⊕ᴰ-elim (λ {
--         nil → roll ∘g σ nil
--       ; cons → roll ∘g σ cons ∘g (liftG ∘g A≅B .fun ∘g lowerG) ,⊗ id })

--     the-B*-alg : Algebra (*Ty B) λ _ → A *
--     the-B*-alg _ = ⊕ᴰ-elim λ {
--         nil → roll ∘g σ nil
--       ; cons → roll ∘g σ cons ∘g (liftG ∘g A≅B .inv ∘g lowerG) ,⊗ id }

--   opaque
--     unfolding ⊗-intro
--     *≅ : A * ≅ B *
--     *≅ .fun = fold*r' A the-A*-alg
--     *≅ .inv = fold*r' B the-B*-alg
--     *≅ .sec =
--       ind-id' (*Ty B) (compHomo (*Ty B) _ the-B*-alg (initialAlgebra (*Ty B))
--         ((λ _ → rec (*Ty A) the-A*-alg _) ,
--         (λ _ → ⊕ᴰ≡ _ _
--           λ @0
--             { nil → refl
--             ; cons → λ i →
--               CONS ∘g
--               (A≅B .sec i ∘g lowerG) ,⊗
--                 (fold*r' A the-A*-alg ∘g lowerG)
--               }))
--         (recHomo (*Ty B) the-B*-alg)) _
--     *≅ .ret =
--       ind-id' (*Ty A) (compHomo (*Ty A) _ the-A*-alg (initialAlgebra (*Ty A))
--         ((λ _ → rec (*Ty B) the-B*-alg _) ,
--         (λ _ → ⊕ᴰ≡ _ _
--           λ @0
--             { nil → refl
--             ; cons → λ i →
--               CONS ∘g
--               (A≅B .ret i ∘g lowerG) ,⊗
--                 (fold*r' B the-B*-alg ∘g lowerG)
--               }))
--         (recHomo (*Ty A) the-A*-alg)) _
