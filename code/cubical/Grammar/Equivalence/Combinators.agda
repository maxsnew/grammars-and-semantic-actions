open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Equivalence.Combinators (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Sum.Binary.Cartesian Alphabet
open import Grammar.KleeneStar.Inductive Alphabet hiding (KL*)
open import Grammar.Sum Alphabet
open import Grammar.Product Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)
open import Grammar.Equivalence.Base Alphabet
open import Term Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  {C : Grammar ℓC}
  {D : Grammar ℓD}
  (A≅B : StrongEquivalence A B)
  (C≅D : StrongEquivalence C D)
  where

  open StrongEquivalence

  opaque
    unfolding _⊗_ ⊗-intro
    concat-strong-equiv : StrongEquivalence (A ⊗ C) (B ⊗ D)
    concat-strong-equiv .fun =
      ⊗-intro (A≅B .fun) (C≅D .fun)
    concat-strong-equiv .inv =
      ⊗-intro (A≅B .inv) (C≅D .inv)
    concat-strong-equiv .sec i = ⊗-intro (A≅B .sec i) (C≅D .sec i)
    concat-strong-equiv .ret i = ⊗-intro (A≅B .ret i) (C≅D .ret i)

  opaque
    unfolding inl
    disjunct-strong-equiv : StrongEquivalence (A ⊕ C) (B ⊕ D)
    disjunct-strong-equiv .fun = ⊕-elim (inl ∘g A≅B .fun) (inr ∘g C≅D .fun)
    disjunct-strong-equiv .inv = ⊕-elim (inl ∘g A≅B .inv) (inr ∘g C≅D .inv)
    disjunct-strong-equiv .sec =
      ⊕≡ _ _
        (λ i → inl ∘g A≅B .sec i)
        (λ i → inr ∘g C≅D .sec i)
    disjunct-strong-equiv .ret =
      ⊕≡ _ _
        (λ i → inl ∘g A≅B .ret i)
        (λ i → inr ∘g C≅D .ret i)

module _
  {A B : Grammar ℓA}
  (A≅B : StrongEquivalence A B)
  where

  open StrongEquivalence

  the-A*-alg : Algebra (*Ty A) λ _ → B *
  the-A*-alg _ = ⊕ᴰ-elim (λ {
      nil → roll ∘g σ nil
    ; cons → roll ∘g σ cons ∘g (liftG ∘g A≅B .fun ∘g lowerG) ,⊗ id })

  the-B*-alg : Algebra (*Ty B) λ _ → A *
  the-B*-alg _ = ⊕ᴰ-elim λ {
      nil → roll ∘g σ nil
    ; cons → roll ∘g σ cons ∘g (liftG ∘g A≅B .inv ∘g lowerG) ,⊗ id }

  opaque
    unfolding _⊗_ ⊗-intro map-id
    star-strong-equiv : StrongEquivalence (A *) (B *)
    star-strong-equiv .fun = fold*r' A the-A*-alg
    star-strong-equiv .inv = fold*r' B the-B*-alg
    star-strong-equiv .sec =
      ind-id' (*Ty B) (compHomo (*Ty B) _ the-B*-alg (initialAlgebra (*Ty B))
        ((λ _ → rec (*Ty A) the-A*-alg _) ,
        (λ _ → ⊕ᴰ≡ _ _
          λ { nil → refl
            ; cons → λ i →
              CONS ∘g
              (A≅B .sec i ∘g lowerG) ,⊗
                (fold*r' A the-A*-alg ∘g lowerG)
              }))
        (recHomo (*Ty B) the-B*-alg)) _
    star-strong-equiv .ret =
      ind-id' (*Ty A) (compHomo (*Ty A) _ the-A*-alg (initialAlgebra (*Ty A))
        ((λ _ → rec (*Ty B) the-B*-alg _) ,
        (λ _ → ⊕ᴰ≡ _ _
          λ { nil → refl
            ; cons → λ i →
              CONS ∘g
              (A≅B .ret i ∘g lowerG) ,⊗
                (fold*r' B the-B*-alg ∘g lowerG)
              }))
        (recHomo (*Ty A) the-A*-alg)) _

  open import Grammar.KleeneStar.Manual Alphabet
  opaque
    unfolding ⊗-intro
    manual-A*-alg : *r-Algebra A
    manual-A*-alg =
      (record { the-ℓ = _
              ; Carrier = KL* B
              ; nil-case = nil
              ; cons-case = cons ∘g ⊗-intro (A≅B .fun) id })

    manual-B*-alg : *r-Algebra B
    manual-B*-alg =
      (record { the-ℓ = _
              ; Carrier = KL* A
              ; nil-case = nil
              ; cons-case = cons ∘g ⊗-intro (A≅B .inv) id })

  opaque
    unfolding manual-A*-alg *r-initial KL*r-elim id*r-AlgebraHom
    manual-star-strong-equiv : StrongEquivalence (KL* A) (KL* B)
    manual-star-strong-equiv .fun = foldKL*r A manual-A*-alg
    manual-star-strong-equiv .inv = foldKL*r B manual-B*-alg
    manual-star-strong-equiv .sec =
      !*r-AlgebraHom B (*r-initial B)
        (record {
          f = foldKL*r A manual-A*-alg ∘g foldKL*r B manual-B*-alg
        ; on-nil = refl
        ; on-cons =
          λ i → cons ∘g ⊗-intro (A≅B .sec i) id ∘g
            ⊗-intro id (foldKL*r A manual-A*-alg ∘g foldKL*r B manual-B*-alg)
        })
        (id*r-AlgebraHom B (*r-initial B))
    manual-star-strong-equiv .ret =
      !*r-AlgebraHom A (*r-initial A)
        (record { f = foldKL*r B manual-B*-alg ∘g foldKL*r A manual-A*-alg
                ; on-nil = refl
                ; on-cons =
                  λ i → cons ∘g ⊗-intro (A≅B .ret i) id ∘g
                    ⊗-intro id (foldKL*r B manual-B*-alg ∘g foldKL*r A manual-A*-alg) })
        (id*r-AlgebraHom A (*r-initial A))
