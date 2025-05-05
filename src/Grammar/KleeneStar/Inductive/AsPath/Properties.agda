{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module @0 Grammar.KleeneStar.Inductive.AsPath.Properties (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet isSetAlphabet
open import Grammar.KleeneStar.Inductive.AsPath.Base Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
open import Grammar.Sum.Properties Alphabet isSetAlphabet
open import Grammar.Epsilon.AsPath.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.AsPath Alphabet isSetAlphabet
open import Grammar.Equivalence.Base Alphabet isSetAlphabet
open import Grammar.Equalizer.AsPath.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Grammar.Inductive.AsPath.Indexed Alphabet isSetAlphabet
open import Grammar.Inductive.AsPath.Properties Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

module _ (A : Grammar ℓA) where
  repeatTy : Lift {j = ℓA} ℕ → Functor (Lift ℕ)
  repeatTy (lift zero) = k ε*
  repeatTy (lift (suc n)) = (k A) ⊗e (Var (lift n))

  repeat' : Lift ℕ → Grammar ℓA
  repeat' n = μ repeatTy n

  open StrongEquivalence

  repeat = ⊕[ n ∈ (Lift ℕ) ] repeat' n

  gradeAlg : Algebra (*Ty A) λ _ → repeat
  gradeAlg _ =
    ⊕ᴰ-elim (λ {
      nil → σ (lift 0) ∘g roll
    ; cons →
        ⊕ᴰ-elim (λ (lift n) → σ (lift (suc n)) ∘g roll ∘g liftG ,⊗ liftG)
        ∘g ⊕ᴰ-distR .fun ∘g lowerG ,⊗ lowerG
    })

  grade : KL* A ⊢ repeat
  grade = rec (*Ty A) gradeAlg _

  ungradeAlg : Algebra repeatTy λ n → (KL* A)
  ungradeAlg (lift zero) = roll ∘g σ nil
  ungradeAlg (lift (suc a)) = roll ∘g σ cons

  ungrade' : ∀ n → repeat' n ⊢ (KL* A)
  ungrade' n = rec repeatTy ungradeAlg n

  ungrade : repeat ⊢ (KL* A)
  ungrade = ⊕ᴰ-elim λ n → ungrade' n

  private
    opaque
      unfolding ⊕ᴰ-distR ⊗-intro eq-π
      the-sec-alg-snd :
        ∀ n →
        (LiftG ℓA A) ⊗ (LiftG ℓA (equalizer (grade ∘g ungrade' (lift n)) (σ (lift n))))
        ⊢
        equalizer (grade ∘g ungrade' (lift (suc n))) (σ (lift (suc n)))
      the-sec-alg-snd n = eq-intro _ _
          (roll ∘g id ,⊗ (liftG ∘g eq-π _ _ ∘g lowerG))
          (λ i → ⊕ᴰ-elim (λ (lift m) → σ (lift (suc m)) ∘g roll ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun ∘g
                 id ,⊗ eq-π-pf _ _ i ∘g lowerG ,⊗ lowerG )
  secAlg : Algebra repeatTy (λ n → equalizer (grade ∘g ungrade' n) (σ n))
  secAlg (lift zero) = eq-intro _ _ roll refl
  secAlg (lift (suc n)) = the-sec-alg-snd n

  *continuous : KL* A ≅ repeat
  *continuous .fun = grade
  *continuous .inv = ungrade
  *continuous .sec = the-sec
    where
    opaque
      unfolding ⊕ᴰ-distR eq-π ⊗-intro eq-intro the-sec-alg-snd
      the-sec : grade ∘g ungrade ≡ id
      the-sec =
        ⊕ᴰ≡ _ _ (λ n →
          equalizer-section (grade ∘g ungrade' n) (σ n)
            (rec repeatTy secAlg n)
            (ind-id' repeatTy
              (compHomo repeatTy
                (initialAlgebra repeatTy)
                secAlg
                (initialAlgebra repeatTy)
                ((λ m → eq-π _ _) ,
                λ { (lift zero) → refl ; (lift (suc m)) → refl })
                (recHomo repeatTy secAlg))
              n))
  *continuous .ret = the-ret
    where
    opaque
      unfolding ⊕ᴰ-distR eq-π ⊗-intro eq-intro
      the-ret : ungrade ∘g grade ≡ id
      the-ret =
        ind-id' (*Ty A)
          (compHomo (*Ty A) (initialAlgebra (*Ty A)) gradeAlg (initialAlgebra (*Ty A))
            ((λ _ → ungrade) ,
            (λ _ → ⊕ᴰ≡ _ _
              λ { nil → refl
                ; cons → refl }))
            (recHomo (*Ty A) gradeAlg)) _

  unrolled* = ⟦ (*Ty A _ ) ⟧ (μ (*Ty A))

  *≅unrolled* : KL* A ≅ unrolled*
  *≅unrolled* = unroll≅ (*Ty A) _

  unrolled*L = ⟦ (*LTy A) _ ⟧ (μ (*LTy A))

  *L≅unrolled*L : *L A ≅ unrolled*L
  *L≅unrolled*L = unroll≅ (*LTy A) _

  repeatTyL : Lift {j = ℓA} ℕ → Functor (Lift ℕ)
  repeatTyL (lift zero) = k ε*
  repeatTyL (lift (suc n)) = (Var (lift n)) ⊗e (k A)

  repeat'L : Lift ℕ → Grammar ℓA
  repeat'L n = μ repeatTyL n

  iterated-tensor : ∀ (n : ℕ) → Grammar ℓA
  iterated-tensor zero = ε*
  iterated-tensor (suc n) = A ⊗ iterated-tensor n

  iterated-tensorL : ∀ (n : ℕ) → Grammar ℓA
  iterated-tensorL zero = ε*
  iterated-tensorL (suc n) = iterated-tensorL n ⊗ A

  repeat'0≅ε : repeat' (lift 0) ≅ ε
  repeat'0≅ε = unroll≅ repeatTy (lift 0) ≅∙ sym≅ (LiftG≅2 _ _ _)

  repeat'L0≅ε : repeat'L (lift 0) ≅ ε
  repeat'L0≅ε = unroll≅ repeatTyL (lift 0) ≅∙ sym≅ (LiftG≅2 _ _ _)

  repeat≅iter : ∀ n → repeat' (lift n) ≅ iterated-tensor n
  repeat≅iter zero = unroll≅ repeatTy (lift 0) ≅∙ sym≅ (LiftG≅ _ _)
  repeat≅iter (suc n) =
    unroll≅ repeatTy (lift (suc n))
    ≅∙ ⊗≅ (sym≅ (LiftG≅ _ _)) (sym≅ (LiftG≅ _ _) ≅∙ repeat≅iter n)

  repeatL≅iterL : ∀ n → repeat'L (lift n) ≅ iterated-tensorL n
  repeatL≅iterL zero = unroll≅ repeatTyL (lift 0) ≅∙ sym≅ (LiftG≅ _ _)
  repeatL≅iterL (suc n) =
    unroll≅ repeatTyL (lift (suc n))
    ≅∙ ⊗≅
      (sym≅ (LiftG≅ _ _) ≅∙ repeatL≅iterL n)
      (sym≅ (LiftG≅ _ _))

  iter≅iterL : ∀ n → iterated-tensor n ≅ iterated-tensorL n
  iter≅iterL zero = id≅
  iter≅iterL (suc zero) =
    ⊗≅ id≅ (sym≅ (LiftG≅ _ _))
    ≅∙ sym≅ εr≅
    ≅∙ εl≅
    ≅∙ ⊗≅ (LiftG≅ _ _) id≅
  iter≅iterL (suc (suc n)) =
    ⊗≅ id≅ (iter≅iterL (suc n))
    ≅∙ ⊗-assoc≅
    ≅∙ ⊗≅ (⊗≅ id≅ (sym≅ (iter≅iterL n))) id≅
    ≅∙ ⊗≅ (iter≅iterL (suc n)) id≅

  repeat'≅repeat'L : ∀ n → repeat' (lift n) ≅ repeat'L (lift n)
  repeat'≅repeat'L n =
    repeat≅iter n
    ≅∙ iter≅iterL n
    ≅∙ sym≅ (repeatL≅iterL n)

  repeatL = ⊕[ n ∈ (Lift ℕ) ] repeat'L n

  repeat≅repeatL : repeat ≅ repeatL
  repeat≅repeatL = ⊕ᴰ≅ (λ (lift n) → repeat'≅repeat'L n)

  *≅repeatL : KL* A ≅ repeatL
  *≅repeatL = *continuous ≅∙ repeat≅repeatL

  gradeLAlg : Algebra (*LTy A) λ _ → repeatL
  gradeLAlg _ = ⊕ᴰ-elim (λ {
      nil → σ (lift 0) ∘g roll
    ; snoc →
      ⊕ᴰ-elim (λ (lift n) → σ (lift (suc n)) ∘g roll ∘g liftG ,⊗ liftG)
      ∘g ⊕ᴰ-distL .fun ∘g lowerG ,⊗ lowerG
    }
    )

  gradeL : *L A ⊢ repeatL
  gradeL = rec (*LTy A) gradeLAlg _

  ungradeAlgL : Algebra repeatTyL λ n → *L A
  ungradeAlgL (lift zero) = roll ∘g σ nil
  ungradeAlgL (lift (suc n)) = roll ∘g σ snoc

  ungrade'L : ∀ n → repeat'L n ⊢ *L A
  ungrade'L n = rec repeatTyL ungradeAlgL n

  ungradeL : repeatL ⊢ *L A
  ungradeL = ⊕ᴰ-elim λ n → ungrade'L n

  private
    opaque
      unfolding ⊕ᴰ-distL ⊗-intro eq-π
      the-sec-alg-sndL :
        ∀ n →
        (LiftG ℓA (equalizer (gradeL ∘g ungrade'L (lift n)) (σ (lift n))))
        ⊗
        (LiftG ℓA A)
        ⊢
        equalizer (gradeL ∘g ungrade'L (lift (suc n))) (σ (lift (suc n)))
      the-sec-alg-sndL n = eq-intro _ _
          (roll ∘g (liftG ∘g eq-π _ _ ∘g lowerG) ,⊗ id)
          (λ i →
            ⊕ᴰ-elim (λ (lift m) → σ (lift (suc m))
            ∘g roll ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distL .fun ∘g
                 eq-π-pf _ _ i ,⊗ id ∘g lowerG ,⊗ lowerG )
  secAlgL :
    Algebra repeatTyL (λ n → equalizer (gradeL ∘g ungrade'L n) (σ n))
  secAlgL (lift zero) = eq-intro _ _ roll refl
  secAlgL (lift (suc n)) = the-sec-alg-sndL n

  *continuousL : *L A ≅ repeatL
  *continuousL .fun = gradeL
  *continuousL .inv = ungradeL
  *continuousL .sec = the-sec
    where
    opaque
      unfolding ⊕ᴰ-distL eq-π ⊗-intro eq-intro the-sec-alg-sndL
      the-sec : gradeL ∘g ungradeL ≡ id
      the-sec =
        ⊕ᴰ≡ _ _ (λ n →
          equalizer-section (gradeL ∘g ungrade'L n) (σ n)
            (rec repeatTyL secAlgL n)
            (ind-id' repeatTyL
              (compHomo repeatTyL
                (initialAlgebra repeatTyL)
                secAlgL
                (initialAlgebra repeatTyL)
                ((λ m → eq-π _ _) ,
                λ { (lift zero) → refl ; (lift (suc m)) → refl })
                (recHomo repeatTyL secAlgL))
              n))
  *continuousL .ret = the-ret
    where
    opaque
      unfolding ⊕ᴰ-distL eq-π ⊗-intro eq-intro
      the-ret : ungradeL ∘g gradeL ≡ id
      the-ret =
        ind-id' (*LTy A)
          (compHomo (*LTy A) (initialAlgebra (*LTy A)) gradeLAlg (initialAlgebra (*LTy A))
            ((λ _ → ungradeL) ,
            (λ _ → ⊕ᴰ≡ _ _
              λ { nil → refl
                ; snoc → refl }))
            (recHomo (*LTy A) gradeLAlg)) _

  *≅*L : KL* A ≅ *L A
  *≅*L = *continuous ≅∙ repeat≅repeatL ≅∙ sym≅ *continuousL

_⊗[_] : Grammar ℓA → ℕ → Grammar ℓA
A ⊗[ n ] = repeat' A (lift n)
