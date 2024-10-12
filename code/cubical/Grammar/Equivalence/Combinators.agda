{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Equivalence.Combinators (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Sum Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)
-- open import Grammar.String.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term Alphabet

private
  variable
    ℓg : Level
    g h k l : Grammar ℓg

module _
  {g h k l : Grammar ℓg}
  (g≅h : StrongEquivalence g h)
  (k≅l : StrongEquivalence k l)
  where

  open StrongEquivalence

  opaque
    unfolding _⊗_ ⊗-intro
    concat-strong-equiv : StrongEquivalence (g ⊗ k) (h ⊗ l)
    concat-strong-equiv .fun =
      ⊗-intro (g≅h .fun) (k≅l .fun)
    concat-strong-equiv .inv =
      ⊗-intro (g≅h .inv) (k≅l .inv)
    concat-strong-equiv .sec i = ⊗-intro (g≅h .sec i) (k≅l .sec i)
    concat-strong-equiv .ret i = ⊗-intro (g≅h .ret i) (k≅l .ret i)

  opaque
    unfolding ⊕-inl
    disjunct-strong-equiv : StrongEquivalence (g ⊕ k) (h ⊕ l)
    disjunct-strong-equiv .fun = ⊕-elim (⊕-inl ∘g g≅h .fun) (⊕-inr ∘g k≅l .fun)
    disjunct-strong-equiv .inv = ⊕-elim (⊕-inl ∘g g≅h .inv) (⊕-inr ∘g k≅l .inv)
    disjunct-strong-equiv .sec =
      ⊕≡ _ _
        (λ i → ⊕-inl ∘g g≅h .sec i)
        (λ i → ⊕-inr ∘g k≅l .sec i)
    disjunct-strong-equiv .ret =
      ⊕≡ _ _
        (λ i → ⊕-inl ∘g g≅h .ret i)
        (λ i → ⊕-inr ∘g k≅l .ret i)

module _
  {g h : Grammar ℓg}
  (g≅h : StrongEquivalence g h)
  where

  open StrongEquivalence

  the-g*-alg : Algebra (*Ty g) λ _ → h *
  the-g*-alg _ = ⊕ᴰ-elim (λ {
      nil → roll ∘g ⊕ᴰ-in nil
    ; cons → roll ∘g ⊕ᴰ-in cons ∘g (liftG ∘g g≅h .fun ∘g lowerG) ,⊗ id })

  the-h*-alg : Algebra (*Ty h) λ _ → g *
  the-h*-alg _ = ⊕ᴰ-elim λ {
      nil → roll ∘g ⊕ᴰ-in nil
    ; cons → roll ∘g ⊕ᴰ-in cons ∘g (liftG ∘g g≅h .inv ∘g lowerG) ,⊗ id }

  star-strong-equiv : StrongEquivalence (g *) (h *)
  star-strong-equiv .fun = fold*r g the-g*-alg
  star-strong-equiv .inv = fold*r h the-h*-alg
  star-strong-equiv .sec =
    ind-id' (*Ty h) (compHomo (*Ty h) _ the-h*-alg (initialAlgebra (*Ty h))
      ((λ _ → rec (*Ty g) the-g*-alg _) ,
      (λ _ → ⊕ᴰ≡ _ _
        λ { nil → refl
          ; cons →
             {!(μ (*Ty g) _)!} ∘g ⊕ᴰ-in cons ∘g {!!} ,⊗ {!!}
            ∘g (liftG ∘g g≅h .fun ∘g lowerG) ,⊗ id
            ∘g (liftG ∘g g≅h .inv ∘g lowerG) ,⊗ id
              ≡⟨ {!!} ⟩
              {!!}
              ≡⟨ {!!} ⟩
            (initialAlgebra (*Ty h) _ ∘g
              map (*Ty h _)
              (λ _ → rec (*Ty g) the-g*-alg _))
             ∘g ⊕ᴰ-in cons
            ∎
            }))
      (recHomo (*Ty h) the-h*-alg)) _
    -- ind-id' _ (compHomo (*Ty h) _ the-h*-alg (initialAlgebra (*Ty h))
    --   ((λ _ → rec (*Ty g) the-g*-alg _) ,
    --   (λ _ → ⊕ᴰ≡ _ _ (λ {
    --     nil → refl
    --   ; cons → λ i → {!CONS!} ∘g g≅h .sec i ,⊗ id ∘g id ,⊗ {!fold*r h the-h*-alg ∘g fold*r h the-h*-alg!} ∘g lowerG ,⊗ lowerG })))
    --   (recHomo (*Ty h) the-h*-alg)) _
  star-strong-equiv .ret = {!!}
  --     !*r-AlgebraHom h (*r-initial h)
  --       (record {
  --         f = foldKL*r g the-g*-alg ∘g foldKL*r h the-h*-alg
  --       ; on-nil = refl
  --       ; on-cons =
  --         λ i → cons ∘g ⊗-intro (g≅h .sec i) id ∘g
  --           ⊗-intro id (foldKL*r g the-g*-alg ∘g foldKL*r h the-h*-alg)
  --       })
  --       (id*r-AlgebraHom h (*r-initial h))
  --   star-strong-equiv .ret =
  --     !*r-AlgebraHom g (*r-initial g)
  --       (record { f = foldKL*r h the-h*-alg ∘g foldKL*r g the-g*-alg
  --               ; on-nil = refl
  --               ; on-cons =
  --                 λ i → cons ∘g ⊗-intro (g≅h .ret i) id ∘g
  --                   ⊗-intro id (foldKL*r h the-h*-alg ∘g foldKL*r g the-g*-alg) })
  --       (id*r-AlgebraHom g (*r-initial g))
