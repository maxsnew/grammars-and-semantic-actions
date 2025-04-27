open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module Grammar.KleeneStar.Inductive.AsEquality.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
-- open import Grammar.Equalizer.Base Alphabet
-- open import Grammar.Lift.Base Alphabet
open import Grammar.Inductive.AsEquality.Indexed Alphabet
-- open import Grammar.Inductive.Properties Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

-- module _ (A : Grammar ℓA) where
--   data *Tag : Type ℓA where
--     nil cons : *Tag

--   *Ty : Unit* {ℓA} → Functor Unit*
--   *Ty _ = ⊕e *Tag (λ { nil → k ε* ; cons → (k A) ⊗e (Var _)})

--   isFinSet*Tag : isFinSet *Tag
--   isFinSet*Tag =
--     EquivPresIsFinSet
--       (isoToEquiv (iso
--         (λ { (inl tt) → nil ; (inr (inl tt)) → cons})
--         (λ { nil → inl tt ; cons → inr (inl tt)})
--         (λ { nil → refl ; cons → refl})
--         λ { (inl tt) → refl ; (inr (inl tt)) → refl}
--         ))
--       (isFinSetFin {n = 2})

--   KL* : Grammar ℓA
--   KL* = μ *Ty _

--   fold*r' : Algebra *Ty (λ _ → B) → KL* ⊢ B
--   fold*r' alg = rec *Ty alg _

--   fold*r : (ε ⊢ B) → A ⊗ B ⊢ B → KL* ⊢ B
--   fold*r [nil] [cons] = fold*r' (λ _ → ⊕ᴰ-elim λ where
--     nil  → [nil] ∘g lowerG ∘g lowerG
--     cons → [cons] ∘g lowerG ,⊗ lowerG)

--   repeatTy : Lift {j = ℓA} ℕ → Functor (Lift ℕ)
--   repeatTy (lift zero) = k ε*
--   repeatTy (lift (suc n)) = (k A) ⊗e (Var (lift n))

--   repeat' : Lift ℕ → Grammar ℓA
--   repeat' n = μ repeatTy n

--   open StrongEquivalence

--   repeat = ⊕[ n ∈ (Lift ℕ) ] repeat' n

--   gradeAlg : Algebra *Ty λ _ → repeat
--   gradeAlg _ = ⊕ᴰ-elim (λ {
--       nil → σ (lift 0) ∘g roll
--     ; cons →
--         ⊕ᴰ-elim (λ (lift n) → σ (lift (suc n)) ∘g roll ∘g liftG ,⊗ liftG)
--         ∘g ⊕ᴰ-distR .fun ∘g lowerG ,⊗ lowerG
--     })

--   grade : KL* ⊢ repeat
--   grade = rec *Ty gradeAlg _

--   ungradeAlg : Algebra repeatTy λ n → KL*
--   ungradeAlg (lift zero) = roll ∘g σ nil
--   ungradeAlg (lift (suc a)) = roll ∘g σ cons

--   ungrade' : ∀ n → repeat' n ⊢ KL*
--   ungrade' n = rec repeatTy ungradeAlg n

--   ungrade : repeat ⊢ KL*
--   ungrade = ⊕ᴰ-elim λ n → ungrade' n

--   private
--     opaque
--       unfolding ⊕ᴰ-distR ⊗-intro eq-π
--       the-sec-alg-snd :
--         ∀ n →
--         (LiftG ℓA A) ⊗ (LiftG ℓA (equalizer (grade ∘g ungrade' (lift n)) (σ (lift n))))
--         ⊢
--         equalizer (grade ∘g ungrade' (lift (suc n))) (σ (lift (suc n)))
--       the-sec-alg-snd n = eq-intro _ _
--           (roll ∘g id ,⊗ (liftG ∘g eq-π _ _ ∘g lowerG))
--           (λ i → ⊕ᴰ-elim (λ (lift m) → σ (lift (suc m)) ∘g roll ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun ∘g
--                  id ,⊗ eq-π-pf _ _ i ∘g lowerG ,⊗ lowerG )

--   secAlg : Algebra repeatTy (λ n → equalizer (grade ∘g ungrade' n) (σ n))
--   secAlg (lift zero) = eq-intro _ _ roll refl
--   secAlg (lift (suc n)) = the-sec-alg-snd n

--   *continuous : KL* ≅ repeat
--   *continuous .fun = grade
--   *continuous .inv = ungrade
--   *continuous .sec = the-sec
--     where
--     opaque
--       unfolding ⊕ᴰ-distR eq-π ⊗-intro eq-intro the-sec-alg-snd
--       the-sec : grade ∘g ungrade ≡ id
--       the-sec =
--         ⊕ᴰ≡ _ _ (λ n →
--           equalizer-section (grade ∘g ungrade' n) (σ n)
--             (rec repeatTy secAlg n)
--             (ind-id' repeatTy
--               (compHomo repeatTy
--                 (initialAlgebra repeatTy)
--                 secAlg
--                 (initialAlgebra repeatTy)
--                 ((λ m → eq-π _ _) ,
--                 λ { (lift zero) → refl ; (lift (suc m)) → refl })
--                 (recHomo repeatTy secAlg))
--               n))
--   *continuous .ret = the-ret
--     where
--     opaque
--       unfolding ⊕ᴰ-distR eq-π ⊗-intro eq-intro
--       the-ret : ungrade ∘g grade ≡ id
--       the-ret =
--         ind-id' *Ty
--           (compHomo *Ty (initialAlgebra *Ty) gradeAlg (initialAlgebra *Ty)
--             ((λ _ → ungrade) ,
--             (λ _ → ⊕ᴰ≡ _ _
--               λ { nil → refl
--                 ; cons → refl }))
--             (recHomo *Ty gradeAlg)) _

--   unrolled* = ⟦ *Ty _ ⟧ (μ *Ty)

--   *≅unrolled* : KL* ≅ unrolled*
--   *≅unrolled* = unroll≅ *Ty _

--   data *TagL : Type ℓA where
--     nil snoc : *TagL

--   *LTy : Unit* {ℓA} → Functor Unit*
--   *LTy _ = ⊕e *TagL (λ { nil → k ε* ; snoc → (Var _) ⊗e (k A)})

--   *LAlg→*Alg : Algebra *LTy (λ _ → B)  → Algebra *Ty (λ _ → B ⟜ B)
--   *LAlg→*Alg l-alg _ = ⊕ᴰ-elim (λ {
--       nil → ⟜-intro-ε id ∘g lowerG ∘g lowerG
--     ; cons →
--       ⟜-intro (
--         ⟜-app
--         ∘g (l-alg _ ∘g σ snoc ∘g liftG ,⊗ liftG) ,⊗ id
--         ∘g ⊗-assoc) ∘g lowerG ,⊗ lowerG
--         })

--   fold*l' : Algebra *LTy (λ _ → B) → KL* ⊢ B
--   fold*l' alg = ⟜-app ∘g (alg _ ∘g σ nil ∘g liftG ∘g liftG) ,⊗ fold*r' (*LAlg→*Alg alg) ∘g ⊗-unit-l⁻

--   fold*l : (ε ⊢ B) → B ⊗ A ⊢ B → KL* ⊢ B
--   fold*l [nil] [snoc] = fold*l' (λ _ → ⊕ᴰ-elim λ where
--     nil  → [nil] ∘g lowerG ∘g lowerG
--     snoc → [snoc] ∘g lowerG ,⊗ lowerG)

--   *L : Grammar ℓA
--   *L = μ *LTy _

--   unrolled*L = ⟦ *LTy _ ⟧ (μ *LTy)

--   *L≅unrolled*L : *L ≅ unrolled*L
--   *L≅unrolled*L = unroll≅ *LTy _

--   repeatTyL : Lift {j = ℓA} ℕ → Functor (Lift ℕ)
--   repeatTyL (lift zero) = k ε*
--   repeatTyL (lift (suc n)) = (Var (lift n)) ⊗e (k A)

--   repeat'L : Lift ℕ → Grammar ℓA
--   repeat'L n = μ repeatTyL n

--   iterated-tensor : ∀ (n : ℕ) → Grammar ℓA
--   iterated-tensor zero = ε*
--   iterated-tensor (suc n) = A ⊗ iterated-tensor n

--   iterated-tensorL : ∀ (n : ℕ) → Grammar ℓA
--   iterated-tensorL zero = ε*
--   iterated-tensorL (suc n) = iterated-tensorL n ⊗ A

--   repeat'0≅ε : repeat' (lift 0) ≅ ε
--   repeat'0≅ε = unroll≅ repeatTy (lift 0) ≅∙ sym≅ (LiftG≅2 _ _ _)

--   repeat'L0≅ε : repeat'L (lift 0) ≅ ε
--   repeat'L0≅ε = unroll≅ repeatTyL (lift 0) ≅∙ sym≅ (LiftG≅2 _ _ _)

--   repeat≅iter : ∀ n → repeat' (lift n) ≅ iterated-tensor n
--   repeat≅iter zero = unroll≅ repeatTy (lift 0) ≅∙ sym≅ (LiftG≅ _ _)
--   repeat≅iter (suc n) =
--     unroll≅ repeatTy (lift (suc n))
--     ≅∙ ⊗≅ (sym≅ (LiftG≅ _ _)) (sym≅ (LiftG≅ _ _) ≅∙ repeat≅iter n)

--   repeatL≅iterL : ∀ n → repeat'L (lift n) ≅ iterated-tensorL n
--   repeatL≅iterL zero = unroll≅ repeatTyL (lift 0) ≅∙ sym≅ (LiftG≅ _ _)
--   repeatL≅iterL (suc n) =
--     unroll≅ repeatTyL (lift (suc n))
--     ≅∙ ⊗≅
--       (sym≅ (LiftG≅ _ _) ≅∙ repeatL≅iterL n)
--       (sym≅ (LiftG≅ _ _))

--   iter≅iterL : ∀ n → iterated-tensor n ≅ iterated-tensorL n
--   iter≅iterL zero = id≅
--   iter≅iterL (suc zero) =
--     ⊗≅ id≅ (sym≅ (LiftG≅ _ _))
--     ≅∙ sym≅ εr≅
--     ≅∙ εl≅
--     ≅∙ ⊗≅ (LiftG≅ _ _) id≅
--   iter≅iterL (suc (suc n)) =
--     ⊗≅ id≅ (iter≅iterL (suc n))
--     ≅∙ ⊗-assoc≅
--     ≅∙ ⊗≅ (⊗≅ id≅ (sym≅ (iter≅iterL n))) id≅
--     ≅∙ ⊗≅ (iter≅iterL (suc n)) id≅

--   repeat'≅repeat'L : ∀ n → repeat' (lift n) ≅ repeat'L (lift n)
--   repeat'≅repeat'L n =
--     repeat≅iter n
--     ≅∙ iter≅iterL n
--     ≅∙ sym≅ (repeatL≅iterL n)

--   repeatL = ⊕[ n ∈ (Lift ℕ) ] repeat'L n

--   repeat≅repeatL : repeat ≅ repeatL
--   repeat≅repeatL = ⊕ᴰ≅ (λ (lift n) → repeat'≅repeat'L n)

--   *≅repeatL : KL* ≅ repeatL
--   *≅repeatL = *continuous ≅∙ repeat≅repeatL

--   gradeLAlg : Algebra *LTy λ _ → repeatL
--   gradeLAlg _ = ⊕ᴰ-elim (λ {
--       nil → σ (lift 0) ∘g roll
--     ; snoc →
--       ⊕ᴰ-elim (λ (lift n) → σ (lift (suc n)) ∘g roll ∘g liftG ,⊗ liftG)
--       ∘g ⊕ᴰ-distL .fun ∘g lowerG ,⊗ lowerG
--     }
--     )

--   gradeL : *L ⊢ repeatL
--   gradeL = rec *LTy gradeLAlg _

--   ungradeAlgL : Algebra repeatTyL λ n → *L
--   ungradeAlgL (lift zero) = roll ∘g σ nil
--   ungradeAlgL (lift (suc n)) = roll ∘g σ snoc

--   ungrade'L : ∀ n → repeat'L n ⊢ *L
--   ungrade'L n = rec repeatTyL ungradeAlgL n

--   ungradeL : repeatL ⊢ *L
--   ungradeL = ⊕ᴰ-elim λ n → ungrade'L n

--   private
--     opaque
--       unfolding ⊕ᴰ-distL ⊗-intro eq-π
--       the-sec-alg-sndL :
--         ∀ n →
--         (LiftG ℓA (equalizer (gradeL ∘g ungrade'L (lift n)) (σ (lift n))))
--         ⊗
--         (LiftG ℓA A)
--         ⊢
--         equalizer (gradeL ∘g ungrade'L (lift (suc n))) (σ (lift (suc n)))
--       the-sec-alg-sndL n = eq-intro _ _
--           (roll ∘g (liftG ∘g eq-π _ _ ∘g lowerG) ,⊗ id)
--           (λ i →
--             ⊕ᴰ-elim (λ (lift m) → σ (lift (suc m))
--             ∘g roll ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distL .fun ∘g
--                  eq-π-pf _ _ i ,⊗ id ∘g lowerG ,⊗ lowerG )

--   secAlgL :
--     Algebra repeatTyL (λ n → equalizer (gradeL ∘g ungrade'L n) (σ n))
--   secAlgL (lift zero) = eq-intro _ _ roll refl
--   secAlgL (lift (suc n)) = the-sec-alg-sndL n

--   *continuousL : *L ≅ repeatL
--   *continuousL .fun = gradeL
--   *continuousL .inv = ungradeL
--   *continuousL .sec = the-sec
--     where
--     opaque
--       unfolding ⊕ᴰ-distL eq-π ⊗-intro eq-intro the-sec-alg-sndL
--       the-sec : gradeL ∘g ungradeL ≡ id
--       the-sec =
--         ⊕ᴰ≡ _ _ (λ n →
--           equalizer-section (gradeL ∘g ungrade'L n) (σ n)
--             (rec repeatTyL secAlgL n)
--             (ind-id' repeatTyL
--               (compHomo repeatTyL
--                 (initialAlgebra repeatTyL)
--                 secAlgL
--                 (initialAlgebra repeatTyL)
--                 ((λ m → eq-π _ _) ,
--                 λ { (lift zero) → refl ; (lift (suc m)) → refl })
--                 (recHomo repeatTyL secAlgL))
--               n))
--   *continuousL .ret = the-ret
--     where
--     opaque
--       unfolding ⊕ᴰ-distL eq-π ⊗-intro eq-intro
--       the-ret : ungradeL ∘g gradeL ≡ id
--       the-ret =
--         ind-id' *LTy
--           (compHomo *LTy (initialAlgebra *LTy) gradeLAlg (initialAlgebra *LTy)
--             ((λ _ → ungradeL) ,
--             (λ _ → ⊕ᴰ≡ _ _
--               λ { nil → refl
--                 ; snoc → refl }))
--             (recHomo *LTy gradeLAlg)) _

--   *≅*L : KL* ≅ *L
--   *≅*L = *continuous ≅∙ repeat≅repeatL ≅∙ sym≅ *continuousL

-- _* : Grammar ℓA → Grammar ℓA
-- A * = KL* A
-- infix 40 _*

-- _+ : Grammar ℓA → Grammar ℓA
-- A + = A ⊗ A *
-- infix 40 _+

-- _+L : Grammar ℓA → Grammar ℓA
-- A +L = A * ⊗ A
-- infix 40 _+L

-- _⊗[_] : Grammar ℓA → ℕ → Grammar ℓA
-- A ⊗[ n ] = repeat' A (lift n)

-- NIL : ∀ {A : Grammar ℓA} → ε ⊢ A *
-- NIL = roll ∘g σ nil ∘g liftG ∘g liftG

-- NIL-L : ∀ {A : Grammar ℓA} → ε ⊢ *L A
-- NIL-L = roll ∘g σ nil ∘g liftG ∘g liftG

-- CONS : ∀ {A : Grammar ℓA} → A ⊗ A * ⊢ A *
-- CONS = roll ∘g σ cons ∘g liftG ,⊗ liftG

-- SNOC : ∀ {A : Grammar ℓA} → *L A ⊗ A ⊢ *L A
-- SNOC = roll ∘g σ snoc ∘g liftG ,⊗ liftG

-- +→* : (A : Grammar ℓA) → A + ⊢ A *
-- +→* A = CONS

-- +-singleton : (A : Grammar ℓA) → A ⊢ A +
-- +-singleton A = id ,⊗ NIL ∘g ⊗-unit-r⁻

-- +L-singleton : (A : Grammar ℓA) → A ⊢ A +L
-- +L-singleton A = NIL ,⊗ id ∘g ⊗-unit-l⁻

-- +-cons : (A : Grammar ℓA) → A ⊗ A + ⊢ A +
-- +-cons A = id ,⊗ +→* A

-- *-singleton : (A : Grammar ℓA) → A ⊢ A *
-- *-singleton A = CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻
