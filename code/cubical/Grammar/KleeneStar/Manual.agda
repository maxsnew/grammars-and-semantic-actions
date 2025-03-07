open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.KleeneStar.Manual (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

module _ (A : Grammar ℓA) where
  data KL* : Grammar ℓA
    where
    nil : ε ⊢ KL*
    cons : A ⊗' KL* ⊢ KL*

  -- I want a non-recursive way to check that a Kleene star is either nil
  -- or cons
  -- This shouldn't be definable via fold, because fold necessitates recursion
  --
  -- If KL* = μ X . ε ⊕ A ⊗ X, then this term is just ⊕-elim on that sum
  opaque
    unfolding _⊗_
    caseKL* :
      ε ⊢ B →
      A ⊗ KL* ⊢ B →
      KL* ⊢ B
    caseKL* eε e* _ (nil _ x) = eε _ x
    caseKL* eε e* _ (cons _ x) = e* _ x

  record *r-Algebra : Typeω where
    field
      the-ℓ : Level
      Carrier : Grammar the-ℓ
      nil-case : ε ⊢ Carrier
      cons-case : A ⊗ Carrier ⊢ Carrier

  open *r-Algebra

  opaque
    unfolding _⊗_
    *r-initial : *r-Algebra
    *r-initial .the-ℓ = _
    *r-initial .Carrier = KL*
    *r-initial .nil-case = nil
    *r-initial .cons-case = cons


  record *r-AlgebraHom (alg alg' : *r-Algebra) : Typeω where
    field
      f : alg .Carrier ⊢ alg' .Carrier
      on-nil : f ∘g alg .nil-case ≡ alg' .nil-case
      on-cons : f ∘g alg .cons-case ≡ alg' .cons-case ∘g ⊗-intro id f

  open *r-AlgebraHom

  module _ (the-alg : *r-Algebra) where
    opaque
      unfolding _⊗_ ⊗-intro *r-initial
      id*r-AlgebraHom : *r-AlgebraHom the-alg the-alg
      id*r-AlgebraHom .f = id
      id*r-AlgebraHom .on-nil = refl
      id*r-AlgebraHom .on-cons = refl

      KL*r-elim : KL* ⊢ the-alg .Carrier
      KL*r-elim _ (nil _ x) = the-alg .nil-case _ x
      KL*r-elim _ (cons _ x) =
        the-alg .cons-case _
          ((x .fst) , ((x .snd .fst) , (KL*r-elim _ (x .snd .snd))))


      ∃*r-AlgebraHom : *r-AlgebraHom *r-initial the-alg
      ∃*r-AlgebraHom .f = KL*r-elim
      ∃*r-AlgebraHom .on-nil = refl
      ∃*r-AlgebraHom .on-cons = refl

      !*r-AlgebraHom' :
        (e e' : *r-AlgebraHom *r-initial the-alg) →
        ∀ w p →
        e .f w p ≡ e' .f w p
      !*r-AlgebraHom' e e' _ (nil _ x) =
        funExt⁻ (funExt⁻ (e .on-nil) _) x ∙
        sym (funExt⁻ (funExt⁻ (e' .on-nil) _) x)
      !*r-AlgebraHom' e e' _ (cons _ x) =
        funExt⁻ (funExt⁻ (e .on-cons) _) x ∙
        (λ i → the-alg .cons-case _
           (x .fst , x .snd .fst ,
           !*r-AlgebraHom' e e' _ (x .snd .snd) i
           )) ∙
        sym (funExt⁻ (funExt⁻ (e' .on-cons) _) x)

      !*r-AlgebraHom :
        (e e' : *r-AlgebraHom *r-initial the-alg) →
        e .f ≡ e' .f
      !*r-AlgebraHom e e' =
        funExt λ w → funExt λ p → !*r-AlgebraHom' e e' w p



  foldKL*r = KL*r-elim

  record *l-Algebra : Typeω where
    field
      the-ℓ : Level
      Carrier : Grammar the-ℓ
      nil-case : ε ⊢ Carrier
      snoc-case : Carrier ⊗ A ⊢ Carrier

  open *l-Algebra

  *l-initial : *l-Algebra
  *l-initial .the-ℓ = _
  *l-initial .Carrier = KL*
  *l-initial .nil-case = nil
  *l-initial .snoc-case = ans
    where
    opaque
      unfolding _⊗_ ⊗-intro
      λalg : *r-Algebra
      λalg .the-ℓ = ℓA
      λalg .Carrier = A ⊸ KL*
      λalg .nil-case =
        ⊸-intro (cons ∘g ⊗-intro id nil ∘g ⊗-unit-r⁻ ∘g ⊗-unit-l)
      λalg .cons-case =
        ⊸-intro (cons ∘g ⊗-intro id ⊸-app ∘g ⊗-assoc⁻)

      ans : KL* ⊗ A ⊢ KL*
      ans = ⊸-intro⁻ (foldKL*r λalg)

  record *l-AlgebraHom (alg alg' : *l-Algebra) : Typeω where
    field
      f : alg .Carrier ⊢ alg' .Carrier
      on-nil : f ∘g alg .nil-case ≡ alg' .nil-case
      on-cons : f ∘g alg .snoc-case ≡ alg' .snoc-case ∘g ⊗-intro f id

  open *l-AlgebraHom

  module _ (the-l-alg : *l-Algebra) where
    λalg : *r-Algebra
    λalg .the-ℓ = the-l-alg .the-ℓ
    λalg .Carrier = the-l-alg .Carrier ⟜ the-l-alg .Carrier
    λalg .nil-case = ⟜-intro ⊗-unit-r
    λalg .cons-case =
      ⟜-intro {C = the-l-alg .Carrier}
        (⟜-app ∘g
        ⊗-intro (the-l-alg .snoc-case) id ∘g
        ⊗-assoc)

    KL*l-elim : KL* ⊢ the-l-alg .Carrier
    KL*l-elim =
      ⟜-app ∘g
      ⊗-intro (the-l-alg .nil-case) (foldKL*r λalg) ∘g
      ⊗-unit-l⁻

    foldKL*l = KL*l-elim

    -- TODO prove initiality for the left handed algebra

opaque
  unfolding _⊗_
  cons' : ε ⊢ A ⊸ KL* A ⊸ KL* A
  cons' = ⊸2-intro-ε cons

  NIL : ε ⊢ KL* A
  NIL = nil

  CONS : A ⊗ KL* A ⊢ KL* A
  CONS = cons
