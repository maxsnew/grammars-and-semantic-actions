open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module Grammar.KleeneStar.Inductive (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Product Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
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

module _ (g : Grammar ℓG) where
  data *Tag : Type ℓG where
    nil cons : *Tag

  *Ty : Unit → Functor Unit ℓG
  *Ty _ = ⊕e *Tag (λ { nil → k ε* ; cons → ⊗e (k g) (Var _)})

  isFinSet*Tag : isFinSet *Tag
  isFinSet*Tag =
    EquivPresIsFinSet
      (isoToEquiv (iso
        (λ { (inl tt) → nil ; (inr (inl tt)) → cons})
        (λ { nil → inl tt ; cons → inr (inl tt)})
        (λ { nil → refl ; cons → refl})
        λ { (inl tt) → refl ; (inr (inl tt)) → refl}
        ))
      (isFinSetFin {n = 2})

  KL* : Grammar ℓG
  KL* = μ *Ty _

  fold*r : Algebra *Ty (λ _ → h) → KL* ⊢ h
  fold*r alg = rec *Ty alg _

  repeatTy : ℕ → Functor ℕ ℓG
  repeatTy (zero) = k ε*
  repeatTy (suc n) = ⊗e (k g) (Var n)

  repeat' : ℕ → Grammar ℓG
  repeat' n = μ repeatTy n

  open StrongEquivalence

  repeat = ⊕[ n ∈ ℕ ] repeat' n

  gradeAlg : Algebra *Ty λ _ → repeat
  gradeAlg _ = ⊕ᴰ-elim (λ {
      nil → ⊕ᴰ-in 0 ∘g roll
    ; cons →
        ⊕ᴰ-elim (λ n → ⊕ᴰ-in (suc n) ∘g roll ∘g liftG ,⊗ liftG)
        ∘g ⊕ᴰ-distR .fun ∘g lowerG ,⊗ lowerG
    })

  grade : KL* ⊢ repeat
  grade = rec *Ty gradeAlg _

  ungradeAlg : Algebra repeatTy λ n → KL*
  ungradeAlg zero = roll ∘g ⊕ᴰ-in nil
  ungradeAlg (suc a) = roll ∘g ⊕ᴰ-in cons

  ungrade' : ∀ n → repeat' n ⊢ KL*
  ungrade' n = rec repeatTy ungradeAlg n

  ungrade : repeat ⊢ KL*
  ungrade = ⊕ᴰ-elim λ n → ungrade' n

  private
    opaque
      unfolding ⊕ᴰ-distR ⊗-intro eq-π
      the-sec-alg-snd :
        ∀ n →
        (LiftG ℓG g) ⊗ (LiftG ℓ-zero (equalizer (grade ∘g ungrade' n) (⊕ᴰ-in n)))
        ⊢
        equalizer (grade ∘g ungrade' (suc n)) (⊕ᴰ-in (suc n))
      the-sec-alg-snd n = eq-intro _ _
          (roll ∘g id ,⊗ (liftG ∘g eq-π _ _ ∘g lowerG))
          (λ i → ⊕ᴰ-elim (λ m → ⊕ᴰ-in (suc m) ∘g roll ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun ∘g
                 id ,⊗ eq-π-pf _ _ i ∘g lowerG ,⊗ lowerG )
  secAlg : Algebra repeatTy (λ n → equalizer (grade ∘g ungrade' n) (⊕ᴰ-in n))
  secAlg zero = eq-intro _ _ roll refl
  secAlg (suc n) = the-sec-alg-snd n

  *continuous : StrongEquivalence KL* repeat
  *continuous .fun = grade
  *continuous .inv = ungrade
  *continuous .sec = the-sec
    where
    opaque
      unfolding ⊕ᴰ-distR eq-π ⊗-intro eq-intro the-sec-alg-snd
      the-sec : grade ∘g ungrade ≡ id
      the-sec =
        ⊕ᴰ≡ _ _ (λ n →
          equalizer-section (grade ∘g ungrade' n) (⊕ᴰ-in n)
            (rec repeatTy secAlg n)
            (ind-id' repeatTy
              (compHomo repeatTy
                (initialAlgebra repeatTy)
                secAlg
                (initialAlgebra repeatTy)
                ((λ m → eq-π _ _) ,
                λ { zero → refl ; (suc m) → refl })
                (recHomo repeatTy secAlg))
              n))
  *continuous .ret = the-ret
    where
    opaque
      unfolding ⊕ᴰ-distR eq-π ⊗-intro eq-intro
      the-ret : ungrade ∘g grade ≡ id
      the-ret =
        ind-id' *Ty
          (compHomo *Ty (initialAlgebra *Ty) gradeAlg (initialAlgebra *Ty)
            ((λ _ → ungrade) ,
            (λ _ → ⊕ᴰ≡ _ _
              λ { nil → refl
                ; cons → refl }))
            (recHomo *Ty gradeAlg)) _

  unrolled* = ⟦ *Ty _ ⟧ (μ *Ty)

  *≅unrolled* : KL* ≅ unrolled*
  *≅unrolled* = unroll≅ *Ty _

  data *TagL : Type ℓG where
    nil snoc : *TagL

  *LTy : Unit → Functor Unit ℓG
  *LTy _ = ⊕e *TagL (λ { nil → k ε* ; snoc → ⊗e (Var _) (k g)})

  *LAlg→*Alg : Algebra *LTy (λ _ → h)  → Algebra *Ty (λ _ → h ⊸ h)
  *LAlg→*Alg l-alg _ = ⊕ᴰ-elim (λ {
      nil → ⊸-intro-ε id ∘g lowerG ∘g lowerG
    ; cons → ⊸-intro (⊸-app ∘g (l-alg _ ∘g ⊕ᴰ-in snoc ∘g liftG ,⊗ liftG) ,⊗ id ∘g ⊗-assoc) ∘g lowerG ,⊗ lowerG })

  fold*l : Algebra *LTy (λ _ → h) → KL* ⊢ h
  fold*l alg = ⊸-app ∘g (alg _ ∘g ⊕ᴰ-in nil ∘g liftG ∘g liftG) ,⊗ fold*r (*LAlg→*Alg alg) ∘g ⊗-unit-l⁻

  *L : Grammar ℓG
  *L = μ *LTy _

  unrolled*L = ⟦ *LTy _ ⟧ (μ *LTy)

  *L≅unrolled*L : *L ≅ unrolled*L
  *L≅unrolled*L = unroll≅ *LTy _

  repeatTyL : ℕ → Functor ℕ ℓG
  repeatTyL zero = k ε*
  repeatTyL (suc n) = ⊗e (Var n) (k g)

  repeat'L : ℕ → Grammar ℓG
  repeat'L n = μ repeatTyL n

  iterated-tensor : ∀ (n : ℕ) → Grammar ℓG
  iterated-tensor zero = ε*
  iterated-tensor (suc n) = g ⊗ iterated-tensor n

  iterated-tensorL : ∀ (n : ℕ) → Grammar ℓG
  iterated-tensorL zero = ε*
  iterated-tensorL (suc n) = iterated-tensorL n ⊗ g

  repeat'0≅ε : repeat' 0 ≅ ε
  repeat'0≅ε = unroll≅ repeatTy 0 ≅∙ sym≅ (LiftG≅2 _ _ _)

  repeat'L0≅ε : repeat'L 0 ≅ ε
  repeat'L0≅ε = unroll≅ repeatTyL 0 ≅∙ sym≅ (LiftG≅2 _ _ _)

  repeat≅iter : ∀ n → repeat' n ≅ iterated-tensor n
  repeat≅iter zero = unroll≅ repeatTy 0 ≅∙ sym≅ (LiftG≅ _ _)
  repeat≅iter (suc n) =
    unroll≅ repeatTy (suc n)
    ≅∙ ⊗≅ (sym≅ (LiftG≅ _ _)) (sym≅ (LiftG≅ _ _) ≅∙ repeat≅iter n)

  repeatL≅iterL : ∀ n → repeat'L n ≅ iterated-tensorL n
  repeatL≅iterL zero = unroll≅ repeatTyL 0 ≅∙ sym≅ (LiftG≅ _ _)
  repeatL≅iterL (suc n) =
    unroll≅ repeatTyL (suc n)
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

  repeat'≅repeat'L : ∀ n → repeat' n ≅ repeat'L n
  repeat'≅repeat'L n =
    repeat≅iter n
    ≅∙ iter≅iterL n
    ≅∙ sym≅ (repeatL≅iterL n)

  repeatL = ⊕[ n ∈ ℕ ] repeat'L n

  repeat≅repeatL : repeat ≅ repeatL
  repeat≅repeatL = ⊕ᴰ≅ (λ n → repeat'≅repeat'L n)

  *≅repeatL : KL* ≅ repeatL
  *≅repeatL = *continuous ≅∙ repeat≅repeatL

  gradeLAlg : Algebra *LTy λ _ → repeatL
  gradeLAlg _ = ⊕ᴰ-elim (λ {
      nil → ⊕ᴰ-in 0 ∘g roll
    ; snoc →
      ⊕ᴰ-elim (λ n → ⊕ᴰ-in (suc n) ∘g roll ∘g liftG ,⊗ liftG)
      ∘g ⊕ᴰ-distL .fun ∘g lowerG ,⊗ lowerG
    }
    )

  gradeL : *L ⊢ repeatL
  gradeL = rec *LTy gradeLAlg _

  ungradeAlgL : Algebra repeatTyL λ n → *L
  ungradeAlgL zero = roll ∘g ⊕ᴰ-in nil
  ungradeAlgL (suc n) = roll ∘g ⊕ᴰ-in snoc

  ungrade'L : ∀ n → repeat'L n ⊢ *L
  ungrade'L n = rec repeatTyL ungradeAlgL n

  ungradeL : repeatL ⊢ *L
  ungradeL = ⊕ᴰ-elim λ n → ungrade'L n

  private
    opaque
      unfolding ⊕ᴰ-distL ⊗-intro eq-π
      the-sec-alg-sndL :
        ∀ n →
        (LiftG ℓ-zero (equalizer (gradeL ∘g ungrade'L n) (⊕ᴰ-in n)))
        ⊗
        (LiftG ℓG g)
        ⊢
        equalizer (gradeL ∘g ungrade'L (suc n)) (⊕ᴰ-in (suc n))
      the-sec-alg-sndL n = eq-intro _ _
          (roll ∘g (liftG ∘g eq-π _ _ ∘g lowerG) ,⊗ id)
          (λ i →
            ⊕ᴰ-elim (λ m → ⊕ᴰ-in (suc m)
            ∘g roll ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distL .fun ∘g
                 eq-π-pf _ _ i ,⊗ id ∘g lowerG ,⊗ lowerG )
  secAlgL :
    Algebra repeatTyL (λ n → equalizer (gradeL ∘g ungrade'L n) (⊕ᴰ-in n))
  secAlgL zero = eq-intro _ _ roll refl
  secAlgL (suc n) = the-sec-alg-sndL n

  *continuousL : *L ≅ repeatL
  *continuousL .fun = gradeL
  *continuousL .inv = ungradeL
  *continuousL .sec = the-sec
    where
    opaque
      unfolding ⊕ᴰ-distL eq-π ⊗-intro eq-intro the-sec-alg-sndL
      the-sec : gradeL ∘g ungradeL ≡ id
      the-sec =
        ⊕ᴰ≡ _ _ (λ n →
          equalizer-section (gradeL ∘g ungrade'L n) (⊕ᴰ-in n)
            (rec repeatTyL secAlgL n)
            (ind-id' repeatTyL
              (compHomo repeatTyL
                (initialAlgebra repeatTyL)
                secAlgL
                (initialAlgebra repeatTyL)
                ((λ m → eq-π _ _) ,
                λ { zero → refl ; (suc m) → refl })
                (recHomo repeatTyL secAlgL))
              n))
  *continuousL .ret = the-ret
    where
    opaque
      unfolding ⊕ᴰ-distL eq-π ⊗-intro eq-intro
      the-ret : ungradeL ∘g gradeL ≡ id
      the-ret =
        ind-id' *LTy
          (compHomo *LTy (initialAlgebra *LTy) gradeLAlg (initialAlgebra *LTy)
            ((λ _ → ungradeL) ,
            (λ _ → ⊕ᴰ≡ _ _
              λ { nil → refl
                ; snoc → refl }))
            (recHomo *LTy gradeLAlg)) _

  *≅*L : KL* ≅ *L
  *≅*L = *continuous ≅∙ repeat≅repeatL ≅∙ sym≅ *continuousL

_* : Grammar ℓG → Grammar ℓG
g * = KL* g

_+ : Grammar ℓG → Grammar ℓG
g + = g ⊗ g *

_+L : Grammar ℓG → Grammar ℓG
g +L = g * ⊗ g

_⊗[_] : Grammar ℓG → ℕ → Grammar ℓG
g ⊗[ n ] = repeat' g n

NIL : ∀ {g : Grammar ℓG} → ε ⊢ g *
NIL = roll ∘g ⊕ᴰ-in nil ∘g liftG ∘g liftG

NIL-L : ∀ {g : Grammar ℓG} → ε ⊢ *L g
NIL-L = roll ∘g ⊕ᴰ-in nil ∘g liftG ∘g liftG

CONS : ∀ {g : Grammar ℓG} → g ⊗ g * ⊢ g *
CONS = roll ∘g ⊕ᴰ-in cons ∘g liftG ,⊗ liftG

SNOC : ∀ {g : Grammar ℓG} → *L g ⊗ g ⊢ *L g
SNOC = roll ∘g ⊕ᴰ-in snoc ∘g liftG ,⊗ liftG

+→* : (g : Grammar ℓG) → g + ⊢ g *
+→* g = CONS

+-singleton : (g : Grammar ℓG) → g ⊢ g +
+-singleton g = id ,⊗ NIL ∘g ⊗-unit-r⁻

+L-singleton : (g : Grammar ℓG) → g ⊢ g +L
+L-singleton g = NIL ,⊗ id ∘g ⊗-unit-l⁻

+-cons : (g : Grammar ℓG) → g ⊗ g + ⊢ g +
+-cons g = id ,⊗ +→* g

*-singleton : (g : Grammar ℓG) → g ⊢ g *
*-singleton g = CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻
