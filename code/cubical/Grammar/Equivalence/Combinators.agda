{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Equivalence.Combinators (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Sum Alphabet
open import Grammar.KleeneStar Alphabet hiding (KL*)
open import Grammar.Dependent Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)
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

  opaque
    unfolding _⊗_ ⊗-intro map-id
    star-strong-equiv : StrongEquivalence (g *) (h *)
    star-strong-equiv .fun = fold*r g the-g*-alg
    star-strong-equiv .inv = fold*r h the-h*-alg
    star-strong-equiv .sec =
      ind-id' (*Ty h) (compHomo (*Ty h) _ the-h*-alg (initialAlgebra (*Ty h))
        ((λ _ → rec (*Ty g) the-g*-alg _) ,
        (λ _ → ⊕ᴰ≡ _ _
          λ { nil → refl
            ; cons → λ i →
              CONS ∘g
              (g≅h .sec i ∘g lowerG) ,⊗
                (fold*r g the-g*-alg ∘g lowerG)
              }))
        (recHomo (*Ty h) the-h*-alg)) _
    star-strong-equiv .ret =
      ind-id' (*Ty g) (compHomo (*Ty g) _ the-g*-alg (initialAlgebra (*Ty g))
        ((λ _ → rec (*Ty h) the-h*-alg _) ,
        (λ _ → ⊕ᴰ≡ _ _
          λ { nil → refl
            ; cons → λ i →
              CONS ∘g
              (g≅h .ret i ∘g lowerG) ,⊗
                (fold*r h the-h*-alg ∘g lowerG)
              }))
        (recHomo (*Ty g) the-g*-alg)) _

  open import Grammar.KleeneStar.Manual Alphabet
  opaque
    unfolding ⊗-intro
    manual-g*-alg : *r-Algebra g
    manual-g*-alg =
      (record { the-ℓ = _
              ; G = KL* h
              ; nil-case = nil
              ; cons-case = cons ∘g ⊗-intro (g≅h .fun) id })

    manual-h*-alg : *r-Algebra h
    manual-h*-alg =
      (record { the-ℓ = _
              ; G = KL* g
              ; nil-case = nil
              ; cons-case = cons ∘g ⊗-intro (g≅h .inv) id })

  opaque
    unfolding manual-g*-alg *r-initial KL*r-elim id*r-AlgebraHom
    manual-star-strong-equiv : StrongEquivalence (KL* g) (KL* h)
    manual-star-strong-equiv .fun = foldKL*r g manual-g*-alg
    manual-star-strong-equiv .inv = foldKL*r h manual-h*-alg
    manual-star-strong-equiv .sec =
      !*r-AlgebraHom h (*r-initial h)
        (record {
          f = foldKL*r g manual-g*-alg ∘g foldKL*r h manual-h*-alg
        ; on-nil = refl
        ; on-cons =
          λ i → cons ∘g ⊗-intro (g≅h .sec i) id ∘g
            ⊗-intro id (foldKL*r g manual-g*-alg ∘g foldKL*r h manual-h*-alg)
        })
        (id*r-AlgebraHom h (*r-initial h))
    manual-star-strong-equiv .ret =
      !*r-AlgebraHom g (*r-initial g)
        (record { f = foldKL*r h manual-h*-alg ∘g foldKL*r g manual-g*-alg
                ; on-nil = refl
                ; on-cons =
                  λ i → cons ∘g ⊗-intro (g≅h .ret i) id ∘g
                    ⊗-intro id (foldKL*r h manual-h*-alg ∘g foldKL*r g manual-g*-alg) })
        (id*r-AlgebraHom g (*r-initial g))
